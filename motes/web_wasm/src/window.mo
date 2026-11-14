/// Page navigation and `location` reads.
///
/// `reload`/`navigate`/`replace` may unload the page, so persist state first.
/// `replace` differs from `navigate` in the browser's history: `replace`
/// overwrites the current entry instead of pushing one, which is what an
/// OAuth callback wants -- otherwise Back would re-run the code exchange that
/// has already consumed its one-time `code`.
///
/// The reads exist because a browser OAuth redirect delivers its result in the
/// URL: atproto returns `code`, `state`, `iss` (and on failure `error`,
/// `error_description`) as query parameters of the page the provider sends the
/// user back to. `search_param` is the accessor that matters -- the one that
/// percent-decodes, so a base64url `code` or a `state` carrying `=` arrives
/// intact.

use lib::ffi {
    window_reload_raw, window_navigate_raw, window_replace_raw,
    location_origin_raw, location_href_raw, location_pathname_raw,
    location_search_raw, location_search_param_raw,
}

/// The page's origin (`https://app.example.com`), the exact string an OAuth
/// `redirect_uri` is built from and the one `client_id` must agree with.
pub def Window.origin : IO String := IO.mk location_origin_raw

/// The full current URL.
pub def Window.href : IO String := IO.mk location_href_raw

/// The path component (`/callback`), without query or fragment.
pub def Window.pathname : IO String := IO.mk location_pathname_raw

/// The raw query string, INCLUDING its leading `?` (or `""` when there is
/// none) -- `location.search` verbatim, so a caller that wants to forward the
/// query can.
pub def Window.search : IO String := IO.mk location_search_raw

/// One query parameter, percent-decoded, or `none` when absent.
///
/// `+` decodes to a space, per `application/x-www-form-urlencoded` -- which is
/// the encoding `URLSearchParams` (and therefore every OAuth server) uses.
/// The FIRST occurrence wins; a repeated parameter is not an error here,
/// because a caller that cares can read `search` directly.
pub def Window.search_param (name : String) : IO (Option String) := do {
    let found <- IO.mk (location_search_param_raw name);
    if String.is_empty found
    then IO.pure Option.none
    else IO.pure (Option.some found)
}

pub def Window.reload : IO Unit := IO.mk window_reload_raw

pub def Window.navigate (url : String) : IO Unit := IO.mk (window_navigate_raw url)

/// Navigate without leaving a history entry -- the right verb for the tail of
/// an OAuth callback, where the `code` has already been spent and must not be
/// re-submitted by a Back button.
pub def Window.replace (url : String) : IO Unit := IO.mk (window_replace_raw url)
