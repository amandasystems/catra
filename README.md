# Catra 
A Princess theory for computing Parikh images of automata, and a tool to use
it.

**Warning**: this is *an active research project*. It is not currently intended
for use by anyone except me!

## Building

Note: this is built using nightly Princess.


```
$ sbt assembly
```

## Running


```
./bin/catra solve-satisfy --timeout 300000 experiments 
```

Some UNIX-y path expansion works (e.g. ~/), but it is difficult to get right in
Java and I suggest you use as non-fancy paths and glob patterns as possible.

## Development

Tests are available using the regular `sbt test`. To measure coverage using
[sbt-coverage](https://github.com/scoverage/sbt-scoverage), use `sbt clean
coverage test` followed by `sbt coverageReport`. Your report is now in
`target/scala-2.*/scoverage-report/index.html`.
