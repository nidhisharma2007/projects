#!/usr/bin/env python3

"""
MarketXY Full QA Bug Discovery Tool
===================================

IMPORTANT:
This tool discovers potential and high-confidence defects.
Automated detection cannot prove every business-logic or UX issue is a bug.
Always manually reproduce findings before submitting them as confirmed bugs.

Every finding is tagged with one of these fixed categories:
    Broken Button or Link
    Page Shows an Error
    Wrong or Missing Data
    Search Not Working
    Form Cannot Be Submitted
    Page Does Not Open
    Mobile Display Problem
    Text Overflow / Off-Screen Content
    Broken Page Design
    Wrong Redirect
    Login or Signup Problem
    Slow or Stuck Page
    Filter or Sorting Problem
    Download or Export Problem
    Browser Compatibility Problem
    Spelling or Grammar Mistake
    SEO or Page Title Problem
    Security or Privacy Problem

Every finding also records:
    issue            - short human summary of what was found
    expected_result  - what should have happened
    actual_result     - what actually happened
    screenshot       - path to a screenshot taken at the moment of detection

Outputs:
    bug_report.json
    bug_report.csv
    bug_report.html
    screenshots/

Usage:
    python sitee-check.py

Optional:
    python sitee-check.py --max-pages 100
    python sitee-check.py --no-multibrowser
    python sitee-check.py --no-interaction
    python sitee-check.py --no-spellcheck
    python sitee-check.py --no-login-check
"""

import argparse
import csv
import hashlib
import html
import json
import os
import re
import time
from collections import defaultdict
from urllib.parse import urljoin, urlparse, urldefrag

from playwright.sync_api import sync_playwright, TimeoutError as PlaywrightTimeoutError


# ============================================================
# CONFIGURATION
# ============================================================

START_URL = "https://marketxy.com/"
ALLOWED_DOMAIN = "marketxy.com"

DESKTOP_VIEWPORTS = [
    {"width": 1440, "height": 900},
    {"width": 1280, "height": 800},
]

MOBILE_VIEWPORTS = [
    {"width": 390, "height": 844},
    {"width": 375, "height": 812},
]

SLOW_PAGE_THRESHOLD_MS = 5000
MAX_INTERACTIVE_ELEMENTS = 30

OUTPUT_DIR = "sitee_results"
SCREENSHOT_DIR = os.path.join(OUTPUT_DIR, "screenshots")

SKIP_EXTENSIONS = {
    ".jpg", ".jpeg", ".png", ".gif", ".webp", ".svg",
    ".ico", ".css", ".js", ".woff", ".woff2", ".ttf",
    ".mp4", ".mp3", ".avi", ".mov", ".zip", ".rar"
}

# Forms containing these words are still tested, but only through the
# dedicated, safe login/signup checker (never through the generic form
# filler, which uses arbitrary text/number/email test data).
SENSITIVE_FORM_WORDS = {
    "login",
    "log-in",
    "signin",
    "sign-in",
    "signup",
    "sign-up",
    "register",
    "password",
}

# Forms containing these words are skipped entirely (real payment /
# donation flows should never be exercised by an automated crawler).
SKIP_FORM_WORDS = {
    "checkout",
    "payment",
    "billing",
    "credit-card",
    "card-number",
    "cvv",
    "donate",
    "purchase"
}

DOWNLOAD_WORDS = {
    "download",
    "export",
    "csv",
    "pdf",
    "xlsx",
    "excel"
}

# Patterns that indicate the page is showing a broken/placeholder value
# rather than real content (e.g. "Price: undefined").
WRONG_DATA_PATTERNS = [
    r"\bundefined\b",
    r"\bNaN\b",
    r"\[object Object\]",
    r"\bnull\b",
]

# Patterns that indicate the page itself is showing an error state.
PAGE_ERROR_PATTERNS = [
    r"internal server error",
    r"application error",
    r"something went wrong",
    r"page not found",
    r"404 not found",
    r"503 service unavailable",
    r"502 bad gateway",
]

COMMON_WORDS_ALLOWLIST = {
    "marketxy",
    "javascript",
    "typescript",
    "html",
    "css",
    "json",
    "api",
    "url",
    "seo",
    "login",
    "signup",
    "signin",
    "email",
    "website",
    "websites",
    "dashboard",
    "analytics",
    "data",
    "ai",
    "domain",
    "domains",
    "csv",
    "pdf",
    "xlsx",
    "http",
    "https",
    "www",
}


# ============================================================
# FIXED BUG CATEGORIES
# ============================================================

CATEGORY = {
    "link_button": "Broken Button or Link",
    "page_error": "Page Shows an Error",
    "wrong_data": "Wrong or Missing Data",
    "search": "Search Not Working",
    "form": "Form Cannot Be Submitted",
    "page_not_open": "Page Does Not Open",
    "mobile": "Mobile Display Problem",
    "overflow": "Text Overflow / Off-Screen Content",
    "design": "Broken Page Design",
    "redirect": "Wrong Redirect",
    "login": "Login or Signup Problem",
    "slow": "Slow or Stuck Page",
    "filter": "Filter or Sorting Problem",
    "download": "Download or Export Problem",
    "browser": "Browser Compatibility Problem",
    "spelling": "Spelling or Grammar Mistake",
    "seo": "SEO or Page Title Problem",
    "security": "Security or Privacy Problem",
}


# ============================================================
# HELPERS
# ============================================================

def ensure_dirs():
    os.makedirs(OUTPUT_DIR, exist_ok=True)
    os.makedirs(SCREENSHOT_DIR, exist_ok=True)


def normalize_url(url):
    if not url:
        return None

    url = urldefrag(url)[0]
    parsed = urlparse(url)

    if parsed.scheme not in ("http", "https"):
        return None

    hostname = parsed.hostname
    if not hostname:
        return None

    hostname = hostname.lower()
    if hostname.startswith("www."):
        hostname = hostname[4:]

    if hostname != ALLOWED_DOMAIN:
        return None

    return url


def is_internal(url):
    return normalize_url(url) is not None


def is_crawlable(url):
    if not is_internal(url):
        return False

    path = urlparse(url).path.lower()

    for ext in SKIP_EXTENSIONS:
        if path.endswith(ext):
            return False

    return True


def safe_text(text, limit=500):
    if not text:
        return ""

    text = re.sub(r"\s+", " ", text)
    return text.strip()[:limit]


def fingerprint(*values):
    raw = "|".join(str(v) for v in values)
    return hashlib.sha256(raw.encode("utf-8", errors="ignore")).hexdigest()[:16]


def take_screenshot(page, prefix):
    """Take a full-page screenshot and return its path, or None on failure."""
    if page is None:
        return None

    try:
        filename = fingerprint(prefix, page.url, time.time()) + ".png"
        path = os.path.join(SCREENSHOT_DIR, filename)
        page.screenshot(path=path, full_page=True)
        return path
    except Exception:
        return None


def add_bug(
    bugs,
    url,
    category,
    issue,
    expected_result,
    actual_result,
    severity="Medium",
    confidence="Medium",
    evidence=None,
    page=None,
    screenshot=None
):
    """
    Record a finding.

    category         - one of the CATEGORY dict values (use CATEGORY["key"])
    issue            - short human summary, e.g. "Contact form submit button does nothing"
    expected_result  - what should have happened
    actual_result    - what was actually observed
    page             - pass the Playwright page to auto-capture a screenshot;
                       or pass `screenshot` directly if one was already taken.
    """
    evidence = evidence or {}

    if screenshot is None and page is not None:
        screenshot = take_screenshot(page, category)

    bug = {
        "id": fingerprint(url, category, issue, expected_result, actual_result),
        "url": url,
        "category": category,
        "issue": issue,
        "expected_result": expected_result,
        "actual_result": actual_result,
        "severity": severity,
        "confidence": confidence,
        "evidence": evidence,
        "screenshot": screenshot,
        "verified": False
    }

    bugs.append(bug)


def unique_bugs(bugs):
    seen = set()
    result = []

    for bug in bugs:
        key = (
            bug["url"],
            bug["category"],
            bug["issue"],
            json.dumps(bug["evidence"], sort_keys=True, default=str)
        )

        if key not in seen:
            seen.add(key)
            result.append(bug)

    return result


# ============================================================
# WRONG / MISSING DATA + PAGE ERROR TEXT
# ============================================================

def check_error_text(page, url, bugs):
    try:
        text = page.inner_text("body")
    except Exception:
        return

    for pattern in WRONG_DATA_PATTERNS:
        matches = re.findall(pattern, text, re.IGNORECASE)

        if matches:
            add_bug(
                bugs, url, CATEGORY["wrong_data"],
                issue=f"Placeholder value '{matches[0]}' visible on page instead of real data",
                expected_result="The page should display real, correctly formatted content with no placeholder or programming artifacts.",
                actual_result=f"The text '{matches[0]}' appeared in the rendered page content.",
                severity="Medium",
                confidence="Medium",
                evidence={"pattern": pattern, "sample": safe_text(text)},
                page=page
            )

    for pattern in PAGE_ERROR_PATTERNS:
        matches = re.findall(pattern, text, re.IGNORECASE)

        if matches:
            add_bug(
                bugs, url, CATEGORY["page_error"],
                issue=f"Error message '{matches[0]}' visible on page",
                expected_result="The page should load normally without displaying an internal error or 'not found' message.",
                actual_result=f"The page body contained the error text '{matches[0]}'.",
                severity="High",
                confidence="Medium",
                evidence={"pattern": pattern, "sample": safe_text(text)},
                page=page
            )


# ============================================================
# SEO
# ============================================================

def check_page_structure(page, url, bugs):
    try:
        title = page.title().strip()

        if not title:
            add_bug(
                bugs, url, CATEGORY["seo"],
                issue="Page is missing a document title",
                expected_result="Every page should have a concise, descriptive <title> tag.",
                actual_result="No page title was found.",
                severity="Medium",
                confidence="High",
                page=page
            )
        elif len(title) > 70:
            add_bug(
                bugs, url, CATEGORY["seo"],
                issue="Page title is unusually long",
                expected_result="Page titles should generally stay under ~60-70 characters so they are not truncated in search results.",
                actual_result=f"Title was {len(title)} characters: \"{title}\"",
                severity="Low",
                confidence="Medium",
                evidence={"title": title, "length": len(title)},
                page=page
            )

        description = page.locator('meta[name="description"]').first.get_attribute("content")

        if not description:
            add_bug(
                bugs, url, CATEGORY["seo"],
                issue="Page is missing a meta description",
                expected_result="Every page should have a meta description summarizing its content.",
                actual_result="No <meta name=\"description\"> tag was found.",
                severity="Low",
                confidence="High",
                page=page
            )

        h1_count = page.locator("h1").count()

        if h1_count == 0:
            add_bug(
                bugs, url, CATEGORY["seo"],
                issue="Page is missing an H1 heading",
                expected_result="Every page should have exactly one H1 heading describing the main content.",
                actual_result="No H1 element was found.",
                severity="Low",
                confidence="High",
                page=page
            )
        elif h1_count > 1:
            add_bug(
                bugs, url, CATEGORY["seo"],
                issue="Page has multiple H1 headings",
                expected_result="A page should have exactly one H1 heading.",
                actual_result=f"{h1_count} H1 elements were found.",
                severity="Low",
                confidence="High",
                evidence={"count": h1_count},
                page=page
            )

    except Exception:
        pass


# ============================================================
# BROKEN IMAGES / BROKEN DESIGN
# ============================================================

def check_images(page, url, bugs):
    try:
        broken = page.evaluate("""
        () => Array.from(document.images)
            .filter(img => img.complete && img.naturalWidth === 0 && img.src)
            .map(img => img.src)
        """)

        for image_url in broken:
            add_bug(
                bugs, url, CATEGORY["design"],
                issue="An image on the page failed to load",
                expected_result="All images should load correctly and display their intended content.",
                actual_result=f"The image at {image_url} failed to render (broken image icon shown).",
                severity="Medium",
                confidence="High",
                evidence={"image_url": image_url},
                page=page
            )

    except Exception:
        pass


# ============================================================
# MOBILE DISPLAY / TEXT OVERFLOW / BROKEN LAYOUT
# ============================================================

def check_overflow(browser, url, bugs, viewports, is_mobile):
    for viewport in viewports:
        context = browser.new_context(viewport=viewport)
        page = context.new_page()

        try:
            page.goto(url, wait_until="domcontentloaded", timeout=20000)
            page.wait_for_timeout(500)

            result = page.evaluate("""
            () => ({
                documentWidth: document.documentElement.scrollWidth,
                viewportWidth: document.documentElement.clientWidth,
                overflow: document.documentElement.scrollWidth >
                          document.documentElement.clientWidth + 5
            })
            """)

            if result["overflow"]:
                category = CATEGORY["mobile"] if is_mobile else CATEGORY["overflow"]

                add_bug(
                    bugs, url, category,
                    issue=f"Page content is wider than the {viewport['width']}px viewport",
                    expected_result=f"At a {viewport['width']}x{viewport['height']} viewport, page content should fit within the screen width with no horizontal scrolling.",
                    actual_result=f"Document width was {result['documentWidth']}px against a viewport width of {result['viewportWidth']}px, causing horizontal overflow.",
                    severity="Medium",
                    confidence="High",
                    evidence={"viewport": viewport, "document_width": result["documentWidth"], "viewport_width": result["viewportWidth"]},
                    page=page
                )

        except Exception:
            pass

        finally:
            context.close()


# ============================================================
# LINK CHECKING (Broken Button or Link)
# ============================================================

def check_links(page, url, links_to_check):
    try:
        links = page.evaluate("""
        () => Array.from(document.querySelectorAll('a[href]')).map(a => ({
            href: a.href,
            text: (a.innerText || '').trim()
        }))
        """)

        for item in links:
            target = normalize_url(item["href"])

            if target and is_crawlable(target):
                links_to_check.append({
                    "source": url,
                    "target": target,
                    "text": safe_text(item["text"], 100)
                })

    except Exception:
        pass


def verify_links(browser, links_to_check, bugs):
    checked = set()

    for item in links_to_check:
        target = item["target"]

        if target in checked:
            continue
        checked.add(target)

        context = browser.new_context()
        page = context.new_page()

        try:
            response = page.goto(target, wait_until="domcontentloaded", timeout=20000)

            if response:
                status = response.status

                if status >= 400:
                    screenshot = take_screenshot(page, "broken_link")

                    add_bug(
                        bugs, item["source"], CATEGORY["link_button"],
                        issue=f"Link \"{item['text'] or target}\" points to a page that errors",
                        expected_result=f"Clicking this link should load {target} successfully.",
                        actual_result=f"The link returned HTTP status {status}.",
                        severity="High" if status >= 500 else "Medium",
                        confidence="High",
                        evidence={"source_url": item["source"], "target_url": target, "link_text": item["text"], "status": status},
                        screenshot=screenshot
                    )

        except Exception as e:
            add_bug(
                bugs, item["source"], CATEGORY["link_button"],
                issue=f"Link \"{item['text'] or target}\" could not be opened",
                expected_result=f"Clicking this link should load {target} successfully.",
                actual_result=f"The page failed to load: {e}",
                severity="Medium",
                confidence="High",
                evidence={"target_url": target, "error": str(e)}
            )

        finally:
            context.close()


# ============================================================
# BUTTON TESTING (Broken Button or Link)
# ============================================================

def test_buttons(page, url, bugs):
    try:
        buttons = page.locator("button, [role='button'], input[type='button'], input[type='submit']")
        count = min(buttons.count(), MAX_INTERACTIVE_ELEMENTS)

        for i in range(count):
            button = buttons.nth(i)

            try:
                if not button.is_visible():
                    continue

                text = safe_text(button.inner_text())
                before_url = page.url
                before = page.evaluate("() => document.body.innerText")

                button.click(timeout=3000)
                page.wait_for_timeout(800)

                after_url = page.url
                after = page.evaluate("() => document.body.innerText")

                changed = before != after or before_url != after_url

                if not changed:
                    # Not automatically a confirmed bug -- low-confidence candidate.
                    add_bug(
                        bugs, url, CATEGORY["link_button"],
                        issue=f"Button \"{text or '(no label)'}\" produced no visible response",
                        expected_result="Clicking the button should change the page content, navigate, or open a dialog/menu.",
                        actual_result="No URL change or visible text change was detected after clicking. Manual verification is required.",
                        severity="Low",
                        confidence="Low",
                        evidence={"button_text": text, "before_url": before_url, "after_url": after_url},
                        page=page
                    )

            except Exception:
                continue

    except Exception:
        pass


# ============================================================
# SEARCH TESTING
# ============================================================

def test_search(page, url, bugs):
    selectors = [
        'input[type="search"]',
        'input[placeholder*="search" i]',
        'input[aria-label*="search" i]',
        'input[name*="search" i]'
    ]

    for selector in selectors:
        try:
            locator = page.locator(selector)

            if locator.count() == 0:
                continue

            search = locator.first

            if not search.is_visible():
                continue

            before = page.locator("body").inner_text()
            before_url = page.url

            search.fill("laptop")
            search.press("Enter")
            page.wait_for_timeout(1500)

            after = page.locator("body").inner_text()
            after_url = page.url

            if before == after and before_url == after_url:
                add_bug(
                    bugs, url, CATEGORY["search"],
                    issue="Search query produced no visible response",
                    expected_result="Submitting a search query (e.g. \"laptop\") should update the page with results or navigate to a results page.",
                    actual_result="No visible content change or URL change was detected after submitting the search.",
                    severity="Medium",
                    confidence="Medium",
                    evidence={"query": "laptop", "before_url": before_url, "after_url": after_url},
                    page=page
                )

            break

        except Exception:
            continue


# ============================================================
# SAFE GENERIC FORM TEST (Form Cannot Be Submitted)
# ============================================================

def test_forms(page, url, bugs):
    try:
        forms = page.locator("form")
        count = forms.count()

        for i in range(count):
            form = forms.nth(i)

            try:
                signature = (
                    (form.get_attribute("id") or "") + " " +
                    (form.get_attribute("action") or "") + " " +
                    (form.get_attribute("class") or "")
                ).lower()

                if any(word in signature for word in SKIP_FORM_WORDS):
                    continue

                # Sensitive (login/signup) forms are handled by test_login_signup instead.
                if any(word in signature for word in SENSITIVE_FORM_WORDS):
                    continue

                inputs = form.locator("input, textarea")

                for j in range(min(inputs.count(), 10)):
                    field = inputs.nth(j)
                    field_type = (field.get_attribute("type") or "text").lower()

                    if field_type in {"hidden", "submit", "button", "checkbox", "radio", "file", "password"}:
                        continue

                    try:
                        if field_type == "email":
                            field.fill("qa-test@example.com")
                        elif field_type == "url":
                            field.fill("https://example.com")
                        elif field_type == "number":
                            field.fill("1")
                        else:
                            field.fill("QA Test Data")
                    except Exception:
                        pass

                submit = form.locator("button[type='submit'], input[type='submit']")

                if submit.count() == 0:
                    continue

                before_url = page.url
                submit.first.click(timeout=3000)
                page.wait_for_timeout(1200)
                after_url = page.url

                if before_url == after_url:
                    add_bug(
                        bugs, url, CATEGORY["form"],
                        issue="Form submission produced no observable response",
                        expected_result="Submitting the form should navigate to a confirmation page, show a success/error message, or otherwise change the page.",
                        actual_result="No URL change or visible feedback was detected after submitting. Manual verification is required.",
                        severity="Low",
                        confidence="Low",
                        evidence={"form": signature},
                        page=page
                    )

            except Exception:
                continue

    except Exception:
        pass


# ============================================================
# LOGIN / SIGNUP TESTING (safe, UX-only)
# ============================================================

def test_login_signup(page, url, bugs):
    """
    Only checks that login/signup forms behave sanely from a UX standpoint:
    - fields render and accept input
    - submitting with empty/dummy data produces some feedback (validation
      message, error, or navigation) rather than doing nothing

    This never attempts to bypass authentication or use real credentials,
    and never tests against third-party accounts.
    """
    try:
        forms = page.locator("form")
        count = forms.count()

        for i in range(count):
            form = forms.nth(i)

            try:
                signature = (
                    (form.get_attribute("id") or "") + " " +
                    (form.get_attribute("action") or "") + " " +
                    (form.get_attribute("class") or "")
                ).lower()

                if not any(word in signature for word in SENSITIVE_FORM_WORDS):
                    continue

                if any(word in signature for word in SKIP_FORM_WORDS):
                    continue

                email_field = form.locator('input[type="email"], input[name*="email" i], input[name*="user" i]').first
                password_field = form.locator('input[type="password"]').first

                has_email = email_field.count() > 0 and email_field.is_visible()
                has_password = password_field.count() > 0 and password_field.is_visible()

                if not (has_email or has_password):
                    continue

                if has_email:
                    try:
                        email_field.fill("qa-test-nonexistent@example.com")
                    except Exception:
                        pass

                if has_password:
                    try:
                        password_field.fill("Dummy-Test-Password-123")
                    except Exception:
                        pass

                submit = form.locator("button[type='submit'], input[type='submit'], button")

                if submit.count() == 0:
                    continue

                before_url = page.url
                before_text = page.locator("body").inner_text()

                submit.first.click(timeout=3000)
                page.wait_for_timeout(1500)

                after_url = page.url
                after_text = page.locator("body").inner_text()

                changed = before_url != after_url or before_text != after_text

                if not changed:
                    add_bug(
                        bugs, url, CATEGORY["login"],
                        issue="Login/signup form gave no feedback after submission",
                        expected_result="Submitting a login or signup form with test credentials should show a validation message, error message, or navigate the user (e.g. 'invalid credentials').",
                        actual_result="No URL change or visible message was detected after submitting. Manual verification is required.",
                        severity="Medium",
                        confidence="Low",
                        evidence={"form": signature, "before_url": before_url, "after_url": after_url},
                        page=page
                    )

            except Exception:
                continue

    except Exception:
        pass


# ============================================================
# FILTER / SORT TESTING
# ============================================================

def test_filters(page, url, bugs):
    try:
        selects = page.locator("select")

        for i in range(min(selects.count(), 10)):
            select = selects.nth(i)

            if not select.is_visible():
                continue

            options = select.locator("option")

            if options.count() < 2:
                continue

            before = page.locator("body").inner_text()
            value = options.nth(1).get_attribute("value")

            if value is None:
                continue

            select.select_option(value=value)
            page.wait_for_timeout(1000)

            after = page.locator("body").inner_text()

            if before == after:
                add_bug(
                    bugs, url, CATEGORY["filter"],
                    issue="Changing a filter/sort control produced no visible change",
                    expected_result="Selecting a different filter or sort option should update the displayed content (e.g. reordered or filtered items).",
                    actual_result="Page content did not change after selecting a different option. Manual verification is required.",
                    severity="Low",
                    confidence="Low",
                    evidence={"selector": "select", "selected_value": value},
                    page=page
                )

    except Exception:
        pass


# ============================================================
# DOWNLOAD TESTING
# ============================================================

def test_downloads(page, url, bugs):
    try:
        candidates = page.locator("a, button")
        count = min(candidates.count(), 50)

        for i in range(count):
            element = candidates.nth(i)

            try:
                if not element.is_visible():
                    continue

                text = safe_text(element.inner_text()).lower()
                href = (element.get_attribute("href") or "").lower()

                if not any(word in text for word in DOWNLOAD_WORDS) and not any(
                    href.endswith(ext) for ext in [".csv", ".pdf", ".xlsx", ".zip"]
                ):
                    continue

                try:
                    with page.expect_download(timeout=5000) as download_info:
                        element.click(timeout=3000)

                    download = download_info.value

                    if download.failure():
                        add_bug(
                            bugs, url, CATEGORY["download"],
                            issue=f"Download \"{text or href}\" failed",
                            expected_result="Clicking this control should successfully download the file.",
                            actual_result=f"The download failed: {download.failure()}",
                            severity="Medium",
                            confidence="High",
                            evidence={"text": text, "error": download.failure()},
                            page=page
                        )

                except PlaywrightTimeoutError:
                    add_bug(
                        bugs, url, CATEGORY["download"],
                        issue=f"Download/export control \"{text or href}\" did not start a download",
                        expected_result="Clicking a download/export control should trigger a file download.",
                        actual_result="No download event occurred within 5 seconds. Manual verification is required.",
                        severity="Low",
                        confidence="Medium",
                        evidence={"text": text, "href": href},
                        page=page
                    )

            except Exception:
                continue

    except Exception:
        pass


# ============================================================
# SECURITY / PRIVACY CONFIGURATION CHECKS
# ============================================================

def check_security(response, url, bugs, page=None):
    if not response:
        return

    try:
        headers = {k.lower(): v for k, v in response.headers.items()}

        security_headers = [
            "content-security-policy",
            "x-content-type-options",
            "referrer-policy"
        ]

        for header in security_headers:
            if header not in headers:
                add_bug(
                    bugs, url, CATEGORY["security"],
                    issue=f"Missing {header} response header",
                    expected_result=f"The server response should include a {header} header to help protect users.",
                    actual_result="Header was not present in the response.",
                    severity="Low",
                    confidence="Medium",
                    evidence={"header": header},
                    page=page
                )

        if url.startswith("https://") and "strict-transport-security" not in headers:
            add_bug(
                bugs, url, CATEGORY["security"],
                issue="Missing HSTS (Strict-Transport-Security) header",
                expected_result="HTTPS responses should include Strict-Transport-Security to prevent protocol downgrade attacks.",
                actual_result="Header was not present in the response.",
                severity="Low",
                confidence="Medium",
                page=page
            )

    except Exception:
        pass


# ============================================================
# SPELLING
# ============================================================

def spellcheck(page, url, bugs):
    try:
        from spellchecker import SpellChecker

        spell = SpellChecker(distance=1)
        text = page.locator("body").inner_text()

        words = re.findall(r"[A-Za-z]+", text)
        words = [w.lower() for w in words if 4 <= len(w) <= 25]
        words = [w for w in words if w not in COMMON_WORDS_ALLOWLIST]

        unknown = spell.unknown(words)
        counts = defaultdict(int)

        for word in words:
            if word in unknown:
                counts[word] += 1

        for word, count in counts.items():
            if count >= 2:
                add_bug(
                    bugs, url, CATEGORY["spelling"],
                    issue=f"Possible spelling error: \"{word}\"",
                    expected_result="Page text should be free of spelling and grammar mistakes.",
                    actual_result=f"The word \"{word}\" was not recognized by the spellchecker and appeared {count} times. Manual verification is required.",
                    severity="Low",
                    confidence="Low",
                    evidence={"word": word, "occurrences": count},
                    page=page
                )

    except ImportError:
        pass
    except Exception:
        pass


# ============================================================
# MAIN CRAWLER
# ============================================================

def crawl(args):
    bugs = []
    visited = set()
    queue = [START_URL]
    links_to_check = []
    pages = []

    with sync_playwright() as p:
        browsers = {}
        browsers["chromium"] = p.chromium.launch(headless=True)

        if not args.no_multibrowser:
            try:
                browsers["firefox"] = p.firefox.launch(headless=True)
            except Exception as e:
                print("Firefox unavailable:", e)

            try:
                browsers["webkit"] = p.webkit.launch(headless=True)
            except Exception as e:
                print("WebKit unavailable:", e)

        primary = browsers["chromium"]

        while queue:
            if args.max_pages and len(visited) >= args.max_pages:
                break

            url = queue.pop(0)
            url = normalize_url(url)

            if not url or url in visited:
                continue

            visited.add(url)
            print(f"[{len(visited)}] Checking {url}")

            context = primary.new_context(viewport=DESKTOP_VIEWPORTS[0], accept_downloads=True)
            page = context.new_page()

            console_errors = []
            failed_requests = []

            page.on("console", lambda msg: console_errors.append(msg.text) if msg.type == "error" else None)
            page.on("pageerror", lambda error: console_errors.append(str(error)))
            page.on("requestfailed", lambda request: failed_requests.append(request.url))

            start = time.time()

            try:
                response = page.goto(url, wait_until="networkidle", timeout=30000)
                load_time = int((time.time() - start) * 1000)
                final_url = page.url

                pages.append({
                    "url": url,
                    "final_url": final_url,
                    "status": response.status if response else None,
                    "load_time_ms": load_time,
                    "console_errors": console_errors,
                    "failed_requests": failed_requests
                })

                if response:
                    if response.status >= 400:
                        add_bug(
                            bugs, url, CATEGORY["page_not_open"],
                            issue=f"Page returned HTTP {response.status}",
                            expected_result="The page should load successfully (HTTP 200).",
                            actual_result=f"The server responded with HTTP status {response.status}.",
                            severity="High",
                            confidence="High",
                            evidence={"status": response.status, "final_url": final_url},
                            page=page
                        )

                    check_security(response, url, bugs, page=page)

                if final_url != url:
                    parsed_final = urlparse(final_url)

                    if parsed_final.hostname and ALLOWED_DOMAIN not in parsed_final.hostname:
                        add_bug(
                            bugs, url, CATEGORY["redirect"],
                            issue="Internal URL redirected to an external domain",
                            expected_result=f"Visiting {url} should stay within the {ALLOWED_DOMAIN} site (or redirect only to another internal page).",
                            actual_result=f"The page redirected to an external URL: {final_url}",
                            severity="Medium",
                            confidence="High",
                            evidence={"original_url": url, "final_url": final_url},
                            page=page
                        )

                if load_time > SLOW_PAGE_THRESHOLD_MS:
                    add_bug(
                        bugs, url, CATEGORY["slow"],
                        issue=f"Page took {load_time}ms to load",
                        expected_result=f"Pages should load in under {SLOW_PAGE_THRESHOLD_MS}ms.",
                        actual_result=f"The page took {load_time}ms to reach a network-idle state.",
                        severity="Medium",
                        confidence="Medium",
                        evidence={"load_time_ms": load_time, "threshold_ms": SLOW_PAGE_THRESHOLD_MS},
                        page=page
                    )

                for error in console_errors:
                    add_bug(
                        bugs, url, CATEGORY["page_error"],
                        issue="JavaScript error occurred while loading the page",
                        expected_result="The page should load without throwing JavaScript errors.",
                        actual_result=f"Console/page error: {error}",
                        severity="Medium",
                        confidence="Medium",
                        evidence={"error": error},
                        page=page
                    )

                for failed in failed_requests:
                    add_bug(
                        bugs, url, CATEGORY["page_error"],
                        issue="A network request failed while loading the page",
                        expected_result="All page resources (scripts, styles, API calls, images) should load successfully.",
                        actual_result=f"Request failed: {failed}",
                        severity="Medium",
                        confidence="Medium",
                        evidence={"request": failed},
                        page=page
                    )

                check_page_structure(page, url, bugs)
                check_error_text(page, url, bugs)
                check_images(page, url, bugs)
                check_links(page, url, links_to_check)

                if not args.no_interaction:
                    test_buttons(page, url, bugs)
                    test_search(page, url, bugs)
                    test_forms(page, url, bugs)
                    test_filters(page, url, bugs)
                    test_downloads(page, url, bugs)

                if not args.no_login_check:
                    test_login_signup(page, url, bugs)

                if not args.no_spellcheck:
                    spellcheck(page, url, bugs)

                # Discover more internal pages
                try:
                    hrefs = page.evaluate("""
                    () => Array.from(document.querySelectorAll('a[href]')).map(a => a.href)
                    """)

                    for href in hrefs:
                        target = normalize_url(href)

                        if target and is_crawlable(target) and target not in visited:
                            queue.append(target)

                except Exception:
                    pass

            except PlaywrightTimeoutError as e:
                add_bug(
                    bugs, url, CATEGORY["page_not_open"],
                    issue="Page failed to load within timeout",
                    expected_result="The page should finish loading within the configured timeout (30s).",
                    actual_result=f"The page did not finish loading: {e}",
                    severity="High",
                    confidence="Medium",
                    evidence={"error": str(e)}
                )

            except Exception as e:
                add_bug(
                    bugs, url, CATEGORY["page_not_open"],
                    issue="Page could not be opened",
                    expected_result="The page should open without error.",
                    actual_result=f"An unexpected error occurred: {e}",
                    severity="High",
                    confidence="High",
                    evidence={"error": str(e)}
                )

            finally:
                context.close()

            # Mobile + desktop layout checks
            check_overflow(primary, url, bugs, MOBILE_VIEWPORTS, is_mobile=True)
            check_overflow(primary, url, bugs, DESKTOP_VIEWPORTS, is_mobile=False)

        print("\nVerifying discovered internal links...")
        verify_links(primary, links_to_check, bugs)

        # Cross browser passive checks
        if not args.no_multibrowser:
            for browser_name in ["firefox", "webkit"]:
                if browser_name not in browsers:
                    continue

                browser = browsers[browser_name]
                print(f"\nRunning {browser_name} checks...")

                for page_data in pages:
                    url = page_data["url"]
                    context = browser.new_context(viewport=DESKTOP_VIEWPORTS[0])
                    page = context.new_page()

                    try:
                        response = page.goto(url, wait_until="domcontentloaded", timeout=30000)

                        if response and response.status >= 400:
                            add_bug(
                                bugs, url, CATEGORY["browser"],
                                issue=f"Page returns HTTP {response.status} in {browser_name}",
                                expected_result=f"The page should load successfully in {browser_name}, matching its behavior in Chromium.",
                                actual_result=f"{browser_name} received HTTP status {response.status}.",
                                severity="Medium",
                                confidence="High",
                                evidence={"browser": browser_name, "status": response.status},
                                page=page
                            )

                        errors = []
                        page.on("pageerror", lambda error: errors.append(str(error)))
                        page.wait_for_timeout(1000)

                        for error in errors:
                            add_bug(
                                bugs, url, CATEGORY["browser"],
                                issue=f"JavaScript error in {browser_name}",
                                expected_result=f"The page should run without JavaScript errors in {browser_name}.",
                                actual_result=f"Error: {error}",
                                severity="Medium",
                                confidence="Medium",
                                evidence={"browser": browser_name, "error": error},
                                page=page
                            )

                    except Exception as e:
                        add_bug(
                            bugs, url, CATEGORY["browser"],
                            issue=f"Page could not load in {browser_name}",
                            expected_result=f"The page should load in {browser_name} the same way it does in Chromium.",
                            actual_result=f"Error: {e}",
                            severity="Medium",
                            confidence="Medium",
                            evidence={"browser": browser_name, "error": str(e)}
                        )

                    finally:
                        context.close()

        for browser in browsers.values():
            browser.close()

    return pages, unique_bugs(bugs)


# ============================================================
# REPORTS
# ============================================================

def write_json(pages, bugs):
    path = os.path.join(OUTPUT_DIR, "bug_report.json")

    with open(path, "w", encoding="utf-8") as f:
        json.dump(
            {"pages_checked": len(pages), "bugs_found": len(bugs), "bugs": bugs},
            f, indent=2, ensure_ascii=False
        )


def write_csv(bugs):
    path = os.path.join(OUTPUT_DIR, "bug_report.csv")

    with open(path, "w", newline="", encoding="utf-8") as f:
        writer = csv.writer(f)

        writer.writerow([
            "Bug ID", "URL", "Category", "Issue",
            "Expected Result", "Actual Result",
            "Severity", "Confidence", "Evidence", "Screenshot", "Verified"
        ])

        for bug in bugs:
            writer.writerow([
                bug["id"],
                bug["url"],
                bug["category"],
                bug["issue"],
                bug["expected_result"],
                bug["actual_result"],
                bug["severity"],
                bug["confidence"],
                json.dumps(bug["evidence"], ensure_ascii=False),
                bug["screenshot"] or "",
                bug["verified"]
            ])


def write_html(bugs):
    path = os.path.join(OUTPUT_DIR, "bug_report.html")
    rows = []

    for bug in bugs:
        evidence = html.escape(json.dumps(bug["evidence"], indent=2, ensure_ascii=False))

        screenshot = ""
        if bug["screenshot"]:
            rel = os.path.relpath(bug["screenshot"], OUTPUT_DIR)
            screenshot = f'<img src="{html.escape(rel)}" style="max-width:320px;display:block;margin-top:6px;">'
        else:
            screenshot = "<i>none</i>"

        rows.append(f"""
            <tr>
                <td>{html.escape(bug['id'])}</td>
                <td><a href="{html.escape(bug['url'])}">{html.escape(bug['url'])}</a></td>
                <td><span class="cat">{html.escape(bug['category'])}</span></td>
                <td>{html.escape(bug['issue'])}</td>
                <td>{html.escape(bug['expected_result'])}</td>
                <td>{html.escape(bug['actual_result'])}</td>
                <td>{html.escape(bug['severity'])}</td>
                <td>{html.escape(bug['confidence'])}</td>
                <td><pre>{evidence}</pre></td>
                <td>{screenshot}</td>
            </tr>
        """)

    document = f"""
    <!DOCTYPE html>
    <html>
    <head>
        <meta charset="UTF-8">
        <title>MarketXY QA Bug Report</title>
        <style>
            body {{ font-family: Arial, sans-serif; margin: 30px; }}
            table {{ border-collapse: collapse; width: 100%; }}
            th, td {{ border: 1px solid #ccc; padding: 10px; vertical-align: top; font-size: 13px; }}
            th {{ background: #eee; }}
            pre {{ white-space: pre-wrap; max-width: 300px; font-size: 11px; }}
            .cat {{ display:inline-block; padding:2px 6px; border-radius:4px; background:#e8f0fe; white-space:nowrap; }}
        </style>
    </head>
    <body>
        <h1>MarketXY QA Bug Report</h1>
        <p>Total findings: <b>{len(bugs)}</b></p>
        <p><b>Important:</b> Findings marked with Low or Medium confidence should be manually reproduced before being reported as confirmed bugs.</p>
        <table>
            <thead>
                <tr>
                    <th>ID</th><th>URL</th><th>Category</th><th>Issue</th>
                    <th>Expected Result</th><th>Actual Result</th>
                    <th>Severity</th><th>Confidence</th><th>Evidence</th><th>Screenshot</th>
                </tr>
            </thead>
            <tbody>
                {"".join(rows)}
            </tbody>
        </table>
    </body>
    </html>
    """

    with open(path, "w", encoding="utf-8") as f:
        f.write(document)


# ============================================================
# ARGUMENTS
# ============================================================

def parse_args():
    parser = argparse.ArgumentParser(description="MarketXY full QA bug discovery crawler")

    parser.add_argument("--max-pages", type=int, default=0,
                         help="Maximum pages to crawl. 0 means crawl until no new internal pages are found.")
    parser.add_argument("--no-multibrowser", action="store_true", help="Only use Chromium.")
    parser.add_argument("--no-interaction", action="store_true",
                         help="Skip interactive button, search, form, filter and download checks.")
    parser.add_argument("--no-spellcheck", action="store_true", help="Skip spelling candidate detection.")
    parser.add_argument("--no-login-check", action="store_true",
                         help="Skip the safe login/signup UX check.")

    return parser.parse_args()


# ============================================================
# MAIN
# ============================================================

def main():
    args = parse_args()
    ensure_dirs()

    print("=" * 60)
    print("MarketXY Full QA Bug Discovery")
    print("=" * 60)
    print(f"Starting URL: {START_URL}")

    if args.max_pages == 0:
        print("Maximum pages: Unlimited until crawl queue is empty")
    else:
        print(f"Maximum pages: {args.max_pages}")

    print()

    pages, bugs = crawl(args)

    write_json(pages, bugs)
    write_csv(bugs)
    write_html(bugs)

    print()
    print("=" * 60)
    print("SCAN COMPLETE")
    print("=" * 60)
    print(f"Pages checked: {len(pages)}")
    print(f"Unique findings: {len(bugs)}")
    print()

    categories = defaultdict(int)
    for bug in bugs:
        categories[bug["category"]] += 1

    for category, count in sorted(categories.items(), key=lambda x: -x[1]):
        print(f"{category}: {count}")

    print()
    print("Reports:")
    print(os.path.join(OUTPUT_DIR, "bug_report.json"))
    print(os.path.join(OUTPUT_DIR, "bug_report.csv"))
    print(os.path.join(OUTPUT_DIR, "bug_report.html"))
    print()
    print("IMPORTANT:")
    print("Manually reproduce each finding before submitting it as a real bug.")


if __name__ == "__main__":
    main()
