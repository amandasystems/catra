#!/usr/bin/env python3
import math
import sys
import re
from collections import Counter, defaultdict

LINE_RE = re.compile(
    r"^==== (?P<file_name>.*?): (?P<sat_status>sat|unsat|timeout.*ms) run: (?P<runtime>[0-9\.]+)s parse: .*====$"
)
THRESHOLD_SECONDS = 2.0
THRESHOLD_PERCENTAGE = 5.0

file_names = sys.argv[1:]


def parse_file(file_name) -> dict[str, tuple[str, float]]:
    results = dict()
    with open(file_name) as f:
        for line in f:
            match = LINE_RE.match(line)
            if not match:
                continue
            sat_status = match.group("sat_status")
            results[match.group("file_name")] = (
                sat_status,
                float(match.group("runtime"))
                if not "timeout" in sat_status
                else float("inf"),
            )
    return results


def describe_cluster(cluster, label):
    if not cluster:
        return []
    name = "/".join(sorted([name for name in cluster]))
    solo_or_shared = "shared" if len(cluster) > 1 else "solo"
    return [f"{name} {solo_or_shared} {label}"]


def classify_outcome(runtimes: list[float]) -> list[str]:
    solver_and_runtime = list(zip(runtimes, file_names))
    solver_and_runtime.sort()

    best_runtime, _ = solver_and_runtime[0]
    worst_runtime, _ = solver_and_runtime[-1]

    if best_runtime == worst_runtime:
        # Catches the case when all are infinite, and the unlikely case when
        # they are the same. Either way, we can stop now -- nobody won!
        return ["all timeout"] if best_runtime == float("inf") else ["draw"]

    # Best value is numeric -- it might be the only one. The following
    # arithmetic requires this!

    min_relative_improvement = best_runtime / (1 - (THRESHOLD_PERCENTAGE / 100))
    winner_threshold_value = max(
        best_runtime + THRESHOLD_SECONDS, min_relative_improvement
    )

    winners = [
        name
        for runtime, name in solver_and_runtime
        if runtime <= winner_threshold_value
    ]

    losers = [
        name
        for runtime, name in solver_and_runtime
        if runtime > winner_threshold_value and not runtime == float("inf")
    ]

    timeout_losers = [
        name for runtime, name in solver_and_runtime if runtime == float("inf")
    ]

    if not losers and not timeout_losers:
        return ["draw"]

    win_description = describe_cluster(winners, "win")
    timeout_description = describe_cluster(timeout_losers, "timeout loss")
    lose_description = describe_cluster(losers, "non-timeout loss")

    return win_description + timeout_description + lose_description


log_to_results = [parse_file(file_name) for file_name in file_names]

instances = [set(r.keys()) for r in log_to_results]
common_instances = instances[0].intersection(*instances[1:])
unshared_instances = set.union(*instances).difference(common_instances)

if unshared_instances:
    different_keys_str = (
        ", ".join(list(unshared_instances)[:5])
        + f" ...and {len(unshared_instances) - 5} more"
        if len(unshared_instances) > 5
        else ", ".join(unshared_instances)
    )
    print(f"W: The following instances are not in all logs:\n{different_keys_str}")
    print(f"I: Proceeding with the {len(common_instances)} common instance(s)...")

outcomes: defaultdict[str, Counter] = defaultdict(Counter)

for instance in common_instances:
    runtimes = [log[instance][1] for log in log_to_results]

    statuses_without_timeouts = list(
        {
            log[instance][0]
            for log in log_to_results
            if "timeout" not in log[instance][0]
        }
    )

    if len(statuses_without_timeouts) > 1:
        # The solvers don't agree: we can't trust the numbers.
        description = "/".join(sorted(statuses_without_timeouts))
        outcomes[f"contested: {description}"]["uncertain"] += 1
        print(f"W: instance {instance} had different results")
        continue

    instance_type = (
        statuses_without_timeouts[0] if statuses_without_timeouts else "unknown"
    )
    outcomes[instance_type].update(classify_outcome(runtimes))

print()
print("======= Summary =======")
for outer_label, counts in outcomes.items():
    print(f"## {outer_label}")
    inner_label_maxlen = max(len(l) for l in counts.keys()) + 4
    for inner_label, count in counts.most_common():
        print(f"{inner_label:{inner_label_maxlen}} {count}")
    print()
