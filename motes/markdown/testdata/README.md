# CommonMark spec fixture

The CommonMark 0.31.2 example corpus: 652 examples, split into three parts.

- Upstream: <https://spec.commonmark.org/0.31.2/spec.json>
- Version: CommonMark 0.31.2 (2024-01-28)
- SHA-256 of the upstream file: `d431b29d97b6f73e69d547109cf5081578fac931e72afe95639ebe766c1b2a20`
- License: the spec and its test corpus are published by the CommonMark
  project under CC-BY-SA 4.0. The parts are included here only as test data.

`commonmark-0.31.2.part1.json` … `.part3.json` are the upstream bytes split
at line boundaries; concatenated they are byte-identical to the upstream
file (`split_fixture.py` asserts this). The harness reads the parts and joins
them before parsing, because the self-hosted compiled backend cannot read a
file over 64 KiB in one go
(`plans/implementations/compiled-read-file-second-chunk.md`). When that bug
is fixed the parts collapse back to one file.

Fields per example: `markdown`, `html`, `example`, `start_line`, `end_line`,
`section`.

`src/tests/conformance_tests.mo` reads the parts from the repository root
(both hosts run tests with the repository root as the working directory), so
the paths are `motes/markdown/testdata/commonmark-0.31.2.part*.json`.

Regenerate (only to move to a new spec version, which needs a plan update):

```bash
curl -fsSL https://spec.commonmark.org/0.31.2/spec.json \
    -o /tmp/commonmark-0.31.2.spec.json
python3 -I tools/split_fixture.py /tmp/commonmark-0.31.2.spec.json
mv /tmp/commonmark-0.31.2*.part*.json motes/markdown/testdata/
```
