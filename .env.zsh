get_benchmark_file() {
  sed -E 's/==== (.*): (timeout|sat|unsat).* ====/\1/'
}
