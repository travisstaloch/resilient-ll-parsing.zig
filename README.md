## About

This is a port from rust to zig of https://github.com/matklad/resilient-ll-parsing/ from the blog post https://matklad.github.io/2023/05/21/resilient-ll-parsing-tutorial.html.

Thanks @matklad for sharing this!

## Run / Test
In the examples folder are 4 .pl files with syntax errors.  The following command prints out a concrete syntax tree resulting from parsing them:
```console
$ zig build run -- examples/1.pl
```
