#!/usr/bin/env python3
import re
from collections import defaultdict, namedtuple
import sys
import statistics

Result = namedtuple("Result", ["file_name", "sat_status", "runtime"])
file_names = sys.argv[1:]

LINE_RE = re.compile(
    r"^==== (?P<file_name>.*?): (?P<sat_status>sat|unsat|timeout.*ms) run: (?P<runtime>[0-9\.]+)s parse: .*====$"
)


def parse_lines(lines):
    for line in lines:
        match = LINE_RE.match(line)
        if not match:
            continue
        sat_status = match.group("sat_status")
        runtime = (
            float(match.group("runtime"))
            if not "timeout" in sat_status
            else float("inf")
        )
        yield Result(
            match.group("file_name"),
            sat_status,
            runtime,
        )


def fmt_result(result: Result):
    if "timeout" in result.sat_status:
        return "-"
    else:
        return f"{result.sat_status:>5} in {result.runtime:02.03f}"


instance_to_results = defaultdict(dict)

for log_name in file_names:
    with open(log_name) as log:
        for result in parse_lines(log):
            instance_to_results[result.file_name][log_name] = result

# print("\t\t".join(["instance", *file_names]))

# for instance, results in instance_to_results.items():
#     print(
#         "\t\t".join(
#             [
#                 instance,
#                 *[fmt_result(results[solver]) for solver in file_names],
#             ]
#         )
#     )

results_by_status: defaultdict[str, defaultdict[str, list[Result]]] = defaultdict(
    lambda: defaultdict(list)
)


def log_name_to_solver(log_name):
    return re.match(r".*-(.*).log", log_name).group(1)


solvers = [log_name_to_solver(log) for log in file_names]

for results in instance_to_results.values():
    for log_name in file_names:
        solver = log_name_to_solver(log_name)
        solver_result_on_instance = results[log_name]
        results_by_status[solver_result_on_instance.sat_status][solver].append(
            solver_result_on_instance
        )


def fmt_row(values):
    return ",".join([str(v) for v in values])

def fmt_results(results) -> str:
    if not results:
        return "-"
    if "timeout" in results[0].sat_status or "error" in results[0].sat_status:
        return str(len(results))
    
    # SAT or UNSAT!
    median_runtime = statistics.median([r.runtime for r in results])
    return f"{len(results)}/{median_runtime:02.03f}"
    
print(fmt_row(["status", *solvers]))

for status, solver_results in results_by_status.items():
    status = status.ljust(7) if not "timeout" in status else "timeout"
    result_set = [fmt_results(solver_results[solver]) for solver in solvers]
    print(fmt_row([status, *result_set]))
