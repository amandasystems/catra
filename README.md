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

## Evaluating

There is also a built-in experiment runner that can be built and executed like so:
```
$ sbt benchmark/assembly
$ java -jar benchmark/target/scala-2.13/catra-benchmark-assembly-$VERSION.jar file1 file2
```

The evaluator will evaluate a number of configurations across all instances, in parallel. It is highly recommended to restart the JVM every once in a while. To do that, you can use `xargs`:
```
$ find basket -type f | xargs -n 10 java -jar runner/target/scala-2.13/catra-benchmark-assembly-$VERSION.jar
```

This is mainly intended for artefact evaluation, and is not meant for end users, hence the sharp edges and nonexistent configuration options.


Of course, you can also run the experiments directly from sbt (quoting the arguments because SBT itself is not so much a few sharp edges as a shuriken):
```
$ sbt "benchmark/run basket" | tee results.log
```

## Validation

Similar to the benchmark runner, there is also a validator that will take a list of (directories of) inputs and validate any results with nuXmv. You can access it using:
```
$ sbt validator/assembly
$ java -jar validator/target/scala-2.13/catra-validate-assembly-$VERSION.jar
```

## Development

Tests are available using the regular `sbt test`. To measure coverage using
[sbt-coverage](https://github.com/scoverage/sbt-scoverage), use `sbt clean
coverage test` followed by `sbt coverageReport`. Your report is now in
`target/scala-2.*/scoverage-report/index.html`.
