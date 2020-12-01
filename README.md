# parikh-theory
A Princess theory for computing Parikh images of automata.

**Warning**: this is *an active research project*. It is not currently intended
for use by anyone except me!

## Building

Note: this is built using nightly Princess.

## Development

Tests are available using the regular `sbt test`. To measure coverage using
[sbt-coverage](https://github.com/scoverage/sbt-scoverage), use `sbt clean
coverage test` followed by `sbt coverageReport`. Your report is now in
`target/scala-2.*/scoverage-report/index.html`.
