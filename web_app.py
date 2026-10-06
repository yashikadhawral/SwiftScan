import argparse
import datetime
import hmac
import ipaddress
import json
import logging
import math
import os
import queue
import re
import shutil
import sys
import threading
import time
from urllib.parse import urlsplit

from flask import (Flask, Response, abort, jsonify, make_response, redirect,
                   render_template, request, send_from_directory)
from markupsafe import escape
from werkzeug.middleware.proxy_fix import ProxyFix

import api_sources
import swiftscan
import swiftscan_logging
from swiftscan_logging import audit

swiftscan_logging.setup_logging()

app = Flask(__name__, template_folder="templates")
logger = logging.getLogger("swiftscan.web")


def _trust_proxy():
    # Render sets RENDER=true automatically; SWIFTSCAN_TRUST_PROXY is a manual opt-in for other hosts.
    return bool(os.environ.get("RENDER")) or os.environ.get(
        "SWIFTSCAN_TRUST_PROXY", "").strip().lower() in ("1", "true", "yes")


if _trust_proxy():
    # Use the X-Forwarded-* headers set by the single proxy in front of us,
    # so request.host / request.is_secure / request.remote_addr reflect the real client.
    app.wsgi_app = ProxyFix(app.wsgi_app, x_for=1, x_proto=1, x_host=1)

# One scan at a time (per process).
scan_semaphore = threading.Semaphore(1)

# Report filenames we will list or serve.
REPORT_FILENAME_REGEX = re.compile(r"^rs\.[a-zA-Z0-9_.-]+$")

COOKIE_NAME = "swiftscan_token"
SESSION_SECONDS = 8 * 3600
KEEPALIVE_SECONDS = 15

LOGIN_MAX_FAILURES = 5
LOGIN_WINDOW_SECONDS = 60
_login_failures = {}
_login_lock = threading.Lock()


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------
def get_reports_dir():
    """Absolute reports directory: $SWIFTSCAN_REPORTS_DIR, else <app dir>/reports.
    Anchored to the app, not the working directory, so reports never end up
    wherever the server happened to be launched from."""
    configured = os.environ.get("SWIFTSCAN_REPORTS_DIR", "").strip()
    return os.path.abspath(configured) if configured else os.path.join(
        os.path.dirname(os.path.abspath(__file__)), "reports")


def _expected_token():
    return os.environ.get("SWIFTSCAN_TOKEN", "").strip()


def _token_matches(candidate, expected):
    return bool(candidate) and hmac.compare_digest(candidate.encode("utf-8"), expected.encode("utf-8"))


def _allow_internal():
    return os.environ.get("SWIFTSCAN_ALLOW_INTERNAL", "").strip().lower() in ("1", "true", "yes")


def _is_loopback_addr(addr):
    try:
        return ipaddress.ip_address((addr or "").split("%", 1)[0]).is_loopback
    except ValueError:
        return False


def _host_is_loopback(host_header):
    host = (host_header or "").strip()
    if host.startswith("["):                       # [::1]:5000
        host = host[1:].split("]", 1)[0]
    elif host.count(":") == 1:                     # name:port / 1.2.3.4:port
        host = host.rsplit(":", 1)[0]
    return host.lower() == "localhost" or _is_loopback_addr(host)


def _is_authenticated():
    expected = _expected_token()
    if not expected:
        return True
    auth_header = request.headers.get("Authorization", "").strip()
    if auth_header.lower().startswith("bearer ") and _token_matches(auth_header[7:].strip(), expected):
        return True
    return _token_matches(request.cookies.get(COOKIE_NAME, "").strip(), expected)


def _is_cross_site():
    """True if the browser says this request was triggered by another site."""
    fetch_site = request.headers.get("Sec-Fetch-Site")
    if fetch_site:
        # Set by the browser and cannot be forged by a web page, so when it is
        # present it is authoritative. (Origin can be "null" on a same-origin form POST
        # because of our Referrer-Policy: no-referrer, so we must not rely on it here.)
        return fetch_site not in ("same-origin", "none")
    # Older browsers without Sec-Fetch-*: fall back to comparing Origin with our host.
    origin = request.headers.get("Origin")
    if origin is not None:
        return origin == "null" or urlsplit(origin).netloc != request.host
    return False


def _wants_json():
    return request.path.startswith("/api/")


def _deny(status, message):
    if _wants_json():
        return jsonify({"error": message}), status
    return Response(message + "\n", status=status, mimetype="text/plain")


def _sse(event):
    return "data: " + json.dumps(event) + "\n\n"


def _sse_error(message):
    return Response(_sse({"event": "fatal_error", "message": message}), mimetype="text/event-stream")


# ---------------------------------------------------------------------------
# Request guards and headers
# ---------------------------------------------------------------------------
@app.before_request
def guard():
    # Liveness probe for Docker/orchestrators: reveals nothing, so it is exempt.
    if request.path == "/healthz":
        return None
    token = _expected_token()

    # No token configured -> local use only.
    if not token and not _host_is_loopback(request.host):
        audit("access_denied", reason="no_token_non_local", client_ip=request.remote_addr, path=request.path)
        return _deny(403, "Access restricted to localhost. Set SWIFTSCAN_TOKEN to allow remote access.")

    # Block other websites from driving this app through the user's browser.
    if (_wants_json() or (request.path == "/login" and request.method == "POST")) and _is_cross_site():
        logger.warning("cross_site denied: path=%s sec_fetch_site=%r origin=%r host=%r",
                       request.path, request.headers.get("Sec-Fetch-Site"),
                       request.headers.get("Origin"), request.host)
        audit("access_denied", reason="cross_site", client_ip=request.remote_addr, path=request.path)
        return _deny(403, "Cross-site requests are not allowed.")

    if token:
        if _wants_json() and not _is_authenticated():
            audit("access_denied", reason="unauthorized", client_ip=request.remote_addr, path=request.path)
            return jsonify({"error": "Unauthorized. Valid SWIFTSCAN_TOKEN required."}), 401
        if request.path == "/" and not _is_authenticated():
            return redirect("/login")
    return None


@app.after_request
def add_security_headers(response):
    response.headers["X-Frame-Options"] = "DENY"
    response.headers["Referrer-Policy"] = "no-referrer"
    response.headers["X-Content-Type-Options"] = "nosniff"
    response.headers["Cross-Origin-Resource-Policy"] = "same-origin"
    response.headers["Content-Security-Policy"] = (
        "default-src 'self'; "
        "script-src 'self' 'unsafe-inline'; "   # TODO: move the inline script to /static and drop this
        "style-src 'self' 'unsafe-inline' https://fonts.googleapis.com; "
        "font-src 'self' https://fonts.gstatic.com; "
        "connect-src 'self'; "
        "object-src 'none'; base-uri 'none'; form-action 'self'; frame-ancestors 'none'"
    )
    if request.path.startswith("/api/") and "Cache-Control" not in response.headers:
        response.headers["Cache-Control"] = "no-store"
    return response


@app.errorhandler(404)
def handle_404(_e):
    return _deny(404, "Not found")


@app.errorhandler(405)
def handle_405(_e):
    return _deny(405, "Method not allowed")


@app.errorhandler(500)
def handle_500(_e):
    return _deny(500, "Internal server error")


# ---------------------------------------------------------------------------
# Login
# ---------------------------------------------------------------------------
def _login_rate_limited(ip):
    now = time.time()
    with _login_lock:
        recent = [t for t in _login_failures.get(ip, []) if now - t < LOGIN_WINDOW_SECONDS]
        _login_failures[ip] = recent
        return len(recent) >= LOGIN_MAX_FAILURES


def _record_login_failure(ip):
    with _login_lock:
        _login_failures.setdefault(ip, []).append(time.time())


_LOGIN_PAGE = """<!DOCTYPE html>
<html>
<head>
<meta charset="UTF-8">
<title>SwiftScan - Login</title>
<style>
body { background:#0B0C0E; color:#B7B9BC; font-family:monospace; display:flex; justify-content:center; align-items:center; height:100vh; margin:0; }
.card { background:#2D2F34; border:1px solid #6C6F75; padding:2rem; border-radius:6px; width:320px; }
h2 { color:#FFEA00; margin-top:0; }
input { width:100%; box-sizing:border-box; background:#0B0C0E; color:#fff; border:1px solid #6C6F75; padding:8px; margin:10px 0; border-radius:4px; }
button { width:100%; background:#FFEA00; color:#0B0C0E; font-weight:bold; border:none; padding:10px; cursor:pointer; border-radius:4px; }
.err { color:#ff4d4d; font-size:12px; margin-bottom:10px; }
</style>
</head>
<body>
<form class="card" method="POST" action="/login">
  <h2>SwiftScan Auth</h2>
  <!--ERROR-->
  <label for="tok">Enter SWIFTSCAN_TOKEN:</label>
  <input type="password" id="tok" name="token" required autofocus>
  <button type="submit">Authenticate</button>
</form>
</body>
</html>"""


def _render_login(error=None, status=200):
    snippet = "<div class='err'>{}</div>".format(escape(error)) if error else ""
    html = _LOGIN_PAGE.replace("<!--ERROR-->", snippet)
    return Response(html, status=status, mimetype="text/html")


@app.route("/login", methods=["GET", "POST"])
def login():
    expected = _expected_token()
    if not expected:
        return redirect("/")
    if request.method != "POST":
        return _render_login()

    ip = request.remote_addr
    if _login_rate_limited(ip):
        audit("login_rate_limited", client_ip=ip)
        return _render_login("Too many attempts. Try again in a minute.", 429)

    if _token_matches(request.form.get("token", "").strip(), expected):
        audit("login_success", client_ip=ip)
        resp = make_response(redirect("/"))
        resp.set_cookie(COOKIE_NAME, expected, httponly=True, samesite="Strict",
                        secure=request.is_secure, max_age=SESSION_SECONDS)
        return resp

    _record_login_failure(ip)
    audit("login_failure", client_ip=ip)
    return _render_login("Invalid authentication token.", 401)


@app.route("/logout")
def logout():
    resp = make_response(redirect("/"))
    resp.delete_cookie(COOKIE_NAME)
    return resp


# ---------------------------------------------------------------------------
# Pages and simple APIs
# ---------------------------------------------------------------------------
@app.route("/")
def index():
    return render_template("index.html")


@app.route("/healthz")
def healthz():
    return jsonify({"status": "ok"})


@app.route("/api/tools")
def api_tools():
    """Return tool availability status for all known security tools."""
    tools_list = []
    seen = set()
    for item in swiftscan.tools_precheck:
        binary = item[0]
        if binary in seen:
            continue
        seen.add(binary)

        avail = shutil.which(binary) is not None
        if not avail and os.name == "nt":
            for ext in (".exe", ".bat", ".cmd"):
                if shutil.which(binary + ext) is not None:
                    avail = True
                    break

        if not avail and binary in ("wget", "host", "whois"):
            avail = True

        if not avail and os.name == "nt" and binary in swiftscan.get_wsl_available_tools():
            avail = True

        tools_list.append({"name": binary, "available": avail})

    tools_list.sort(key=lambda t: (not t["available"], t["name"]))
    return jsonify({
        "tools": tools_list,
        "total_checks": len(swiftscan.tool_names),
        "platform": sys.platform,
    })


# ---------------------------------------------------------------------------
# Reports (#16 severity labels, #18 written by the scan thread)
# ---------------------------------------------------------------------------
def write_reports(target, run_stamp, findings, complete_event):
    """Write the text, OSINT and JSON reports. Each is attempted independently,
    so one failure never costs you the others. Returns the file names."""
    reports_dir = get_reports_dir()
    os.makedirs(reports_dir, exist_ok=True)
    names = {
        "vulreport": "rs.vul.%s.%s" % (target, run_stamp),
        "apireport": "rs.api.%s.%s" % (target, run_stamp),
        "jsonreport": "rs.json.%s.%s.json" % (target, run_stamp),
    }

    try:
        with open(os.path.join(reports_dir, names["vulreport"]), "w", encoding="utf-8") as rf:
            rf.write("SwiftScan Vulnerability Report\nTarget: {}\nDate: {}\n\n".format(target, run_stamp))
            for f in findings:
                rf.write("Vulnerability: {}\nSeverity: {}\nModule: {}\nDefinition: {}\nRemediation: {}\nReference: {}\n".format(
                    f.get("title"), swiftscan.severity_label(f.get("severity")), f.get("module") or "n/a",
                    f.get("definition"), f.get("remediation"), f.get("cwe") or "N/A"))
                rf.write("-" * 40 + "\n\n")
    except OSError as err:
        logger.error("Error writing vulreport: %s", err)

    try:
        with open(os.path.join(reports_dir, names["apireport"]), "w", encoding="utf-8") as rf:
            rf.write("SwiftScan OSINT Report\nTarget: {}\nDate: {}\n\n".format(target, run_stamp))
            for finding in complete_event.get("api_findings", []):
                rf.write("=== {} ===\n".format(finding.get("source")))
                if finding.get("ok"):
                    for k, val in (finding.get("data") or {}).items():
                        rf.write("{}: {}\n".format(k, val))
                else:
                    rf.write("{}: {}\n".format(api_sources.status_label(finding), finding.get("reason")))
                rf.write("\n")
    except OSError as err:
        logger.error("Error writing apireport: %s", err)

    try:
        payload = {
            "target": target,
            "scanned_at": run_stamp,
            "total_elapsed_seconds": complete_event.get("total_elapsed", 0),
            "checks_run": complete_event.get("checks_run", 0),
            "checks_skipped": complete_event.get("checks_skipped", 0),
            "budget_exhausted": complete_event.get("budget_exhausted", False),
            "vulnerabilities_found": len(findings),
            "findings": findings,
            "api_findings": complete_event.get("api_findings", []),
        }
        with open(os.path.join(reports_dir, names["jsonreport"]), "w", encoding="utf-8") as rf:
            json.dump(payload, rf, indent=2)
    except OSError as err:
        logger.error("Error writing jsonreport: %s", err)

    return names


@app.route("/api/reports")
def api_reports():
    reports_dir = get_reports_dir()
    if not os.path.isdir(reports_dir):
        return jsonify([])
    files = [f for f in os.listdir(reports_dir)
             if REPORT_FILENAME_REGEX.match(f) and os.path.isfile(os.path.join(reports_dir, f))]
    return jsonify(sorted(files, reverse=True))


@app.route("/api/reports/<path:filename>")
def download_report(filename):
    """Serve a generated report: strict filename allowlist + send_from_directory."""
    if ".." in filename or not REPORT_FILENAME_REGEX.match(filename):
        abort(404)
    response = send_from_directory(get_reports_dir(), filename, as_attachment=False, mimetype="text/plain")
    response.headers["X-Content-Type-Options"] = "nosniff"
    return response


# ---------------------------------------------------------------------------
# Scan streaming
# ---------------------------------------------------------------------------
def _parse_scan_params():
    """Validate budget / timeout / skip. Returns (params, error_message)."""
    try:
        budget_val = float(request.args.get("budget", 15))
        if not math.isfinite(budget_val) or budget_val <= 0:
            raise ValueError("Budget must be a finite number greater than 0.")
        budget_minutes = min(60.0, max(1.0, budget_val))
    except (ValueError, TypeError) as e:
        return None, "Invalid budget: {}".format(e)

    default_timeout = min(300, max(10, int(budget_minutes * 60)))
    try:
        timeout_val = int(request.args.get("timeout", default_timeout))
        if timeout_val <= 0:
            raise ValueError("Timeout must be greater than 0.")
        tool_timeout = min(300, max(10, timeout_val))
    except (ValueError, TypeError) as e:
        return None, "Invalid timeout: {}".format(e)

    allowed_tools = {item[0] for item in swiftscan.tools_precheck}
    skip_set = set()
    for tool_name in request.args.get("skip", "").split(","):
        tool_name = tool_name.strip()
        if not tool_name:
            continue
        if tool_name not in allowed_tools:
            return None, "Invalid skip tool '{}'. Only tools in tools_precheck are allowed.".format(tool_name)
        skip_set.add(tool_name)

    return {"budget_minutes": budget_minutes, "tool_timeout": tool_timeout, "skip": skip_set}, None


def _scan_worker(events, target, params, client_ip):
    """Run the scan to completion and write its reports, whether or not anyone
    is still listening. Always releases the scan slot, then signals the end."""
    run_stamp = datetime.datetime.now().strftime("%Y-%m-%d_%H%M%S")
    findings = []
    started = time.time()
    try:
        for event in swiftscan.run_scan(target, skip=params["skip"], tool_timeout=params["tool_timeout"],
                                        max_total_seconds=params["budget_minutes"] * 60):
            if event.get("event") == "tool_result" and event.get("vulnerable"):
                findings.append(event)
            if event.get("event") == "scan_complete":
                event["reports"] = write_reports(target, run_stamp, findings, event)
                audit("scan_completed", client_ip=client_ip, target=target,
                      checks_run=event.get("checks_run"), checks_skipped=event.get("checks_skipped"),
                      vulnerabilities_found=len(findings), budget_exhausted=event.get("budget_exhausted", False),
                      seconds=round(time.time() - started, 1))
            events.put(event)
    except Exception:  # noqa: BLE001 - the worker must never die silently
        logger.exception("Scan of %s crashed", target)
        audit("scan_crashed", client_ip=client_ip, target=target)
        events.put({"event": "fatal_error", "message": "Scan failed unexpectedly. See the server log."})
    finally:
        scan_semaphore.release()
        events.put(None)


def _stream_events(events):
    while True:
        try:
            event = events.get(timeout=KEEPALIVE_SECONDS)
        except queue.Empty:
            yield ": keep-alive\n\n"   # SSE comment; stops proxies timing out an idle stream
            continue
        if event is None:
            return
        yield _sse(event)


@app.route("/api/scan/stream")
def scan_stream():
    """Start a scan and stream its events (Server-Sent Events)."""
    client_ip = request.remote_addr
    raw_target = request.args.get("target", "").strip()

    # 1. Consent (an audit/UX control: the client supplies it, so it is evidence, not protection)
    if request.args.get("consent", "").strip() not in ("1", "true", "yes"):
        audit("scan_rejected", reason="no_consent", client_ip=client_ip, target=raw_target, consent=False)
        return _sse_error("Authorization consent required. You must certify authorization to test this target.")

    # 2. Target
    if not raw_target:
        return _sse_error("Target cannot be empty.")
    try:
        target = swiftscan.url_maker(raw_target, allow_internal=_allow_internal())
    except ValueError as e:
        audit("scan_rejected", reason="invalid_target", client_ip=client_ip, target=raw_target, consent=True)
        return _sse_error(str(e))

    # 3. Parameters
    params, error = _parse_scan_params()
    if error:
        return _sse_error(error)

    # 4. Slot (acquired before any thread/generator exists, so it cannot leak)
    if not scan_semaphore.acquire(blocking=False):
        audit("scan_rejected", reason="busy", client_ip=client_ip, target=target, consent=True)
        return _sse_error("Server is busy. Another scan is currently in progress.")

    audit("scan_started", client_ip=client_ip, target=target, consent=True,
          budget_minutes=params["budget_minutes"], tool_timeout=params["tool_timeout"],
          skip=sorted(params["skip"]))
    events = queue.Queue()
    try:
        threading.Thread(target=_scan_worker, args=(events, target, params, client_ip),
                         name="swiftscan-scan", daemon=True).start()
    except RuntimeError:                      # could not start a thread: give the slot back
        scan_semaphore.release()
        raise

    response = Response(_stream_events(events), mimetype="text/event-stream")
    response.headers["Cache-Control"] = "no-cache"
    response.headers["X-Accel-Buffering"] = "no"
    return response


# ---------------------------------------------------------------------------
# Entry point
# ---------------------------------------------------------------------------
def run_web(host="127.0.0.1", port=5000, debug=False):
    token = _expected_token()
    public = not _is_loopback_addr(host) and host != "localhost"
    if public and not token:
        logger.error("Binding to %s requires SWIFTSCAN_TOKEN to be set.", host)
        print(f"\n[!] ERROR: Binding to {host} requires the SWIFTSCAN_TOKEN environment variable for security.\n")
        sys.exit(1)
    if debug and public:
        print("\n[!] ERROR: --debug exposes the Werkzeug debugger (remote code execution) and is only allowed on loopback.\n")
        sys.exit(1)

    print(f"\n[+] SwiftScan Web UI starting on http://{host}:{port}")
    if token:
        print("[+] Authentication enabled (SWIFTSCAN_TOKEN configured).")
    else:
        print("[+] No SWIFTSCAN_TOKEN set: only requests from localhost are accepted.")
    print("[+] Open your browser to begin vulnerability scanning.\n")
    app.run(host=host, port=port, debug=debug, threaded=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="SwiftScan Web UI")
    parser.add_argument("--host", default="127.0.0.1", help="Host interface to bind (default: 127.0.0.1)")
    parser.add_argument("--port", type=int, default=int(os.environ.get("PORT", 5000)), help="Port to bind (default: 5000)")
    parser.add_argument("--debug", action="store_true", help="Enable debug mode (loopback only)")
    args = parser.parse_args()
    run_web(host=args.host, port=args.port, debug=args.debug)
