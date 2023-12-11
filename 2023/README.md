Most executables take input from standard in[^1]. For example, to build and run `P10` on `path/to/input.txt`:

```
lake exe P10 < path/to/input.txt
```

To build all executables:
```
lake build
```

[^1]: Except for a few ones where I skipped parsing and massaged the question's inputs into code directly.
