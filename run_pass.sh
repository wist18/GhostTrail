#!/bin/bash

run_task() {
  task run-pass
  return $?
}

while true; do
  run_task
  status=$?
  if [ $status -eq 0 ]; then
    echo "All files have been processed successfully."
    break
  elif [ $status -eq 137 ]; then
    echo "Process was killed due to OOM. Exiting."
    exit 137
  else
    echo "Some files are still unprocessed. Rerunning the task..."
    sleep 0.2  # Delay before rerunning
  fi
done
