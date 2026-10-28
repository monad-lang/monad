# CommonMark spec fixture

`commonmark-0.31.2.spec.json` is the CommonMark 0.31.2 example corpus, 652
examples, unmodified.

- Upstream: <https://spec.commonmark.org/0.31.2/spec.json>
- Version: CommonMark 0.31.2 (2024-01-28)
- SHA-256: `d431b29d97b6f73e69d547109cf5081578fac931e72afe95639ebe766c1b2a20`
- License: the spec and its test corpus are published by the CommonMark
  project under CC-BY-SA 4.0. The JSON is included here only as test data.

Fields per example: `markdown`, `html`, `example`, `start_line`, `end_line`,
`section`.

`src/tests/conformance_tests.mo` reads this file from the repository root
(both hosts run tests with the repository root as the working directory), so
the path is `motes/markdown/testdata/commonmark-0.31.2.spec.json`.

Regenerate (only to move to a new spec version, which needs a plan update):

```bash
curl -fsSL https://spec.commonmark.org/0.31.2/spec.json \
    -o motes/markdown/testdata/commonmark-0.31.2.spec.json
```
