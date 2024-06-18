import subprocess
import time
import os
import re
import json
from dotenv import load_dotenv

# Load the .env file
load_dotenv()

# Get the LINUX_VERSION environment variable
linux_version = os.getenv('LINUX_VERSION')

# Create the directory paths
bc_dir = f"linux-{linux_version}-bc"
ll_dir = f"linux-{linux_version}-ll"

# Directory containing the files
txt_dir = 'passes-out'

# Output file
stats_dir = 'stats.json'

patterns = {
    'lock': ['mutex_lock', 'spin_lock', 'semaphore_lock'],
    'unlock': ['mutex_unlock', 'spin_unlock', 'semaphore_unlock']
}

def run_task():
    result = subprocess.run(["task", "run-pass"], capture_output=True)
    return result.returncode

def count_files(directory):
    return sum(len(files) for _, _, files in os.walk(directory))

def print_loading_bar(processed, total):
    bar_length = 40
    progress = processed / total
    block = int(bar_length * progress)
    bar = '#' * block + '-' * (bar_length - block)
    print(f'\r[{bar}] {processed}/{total} files processed', end='', flush=True)

# Function to extract the number of SCUAF gadgets from a single line
def extract_gadgets(line):
    match = re.search(r'Found: (\d+) SCUAF gadgets', line)
    if match:
        return int(match.group(1))
    return 0

# Function to extract lock function types from a single line
def extract_lock_func(line):
    match = re.search(r'\block_func=(\w+)', line)
    if match:
        return match.group(1)
    return None

# Function to extract unlock function types from a single line
def extract_unlock_func(line):
    match = re.search(r'\bunlock_func=(\w+)', line)
    if match:
        return match.group(1)
    return None

# Function to process all files in a directory and subdirectories to sum up the SCUAF gadgets and lock/unlock function types
def process_files(directory):
    total_gadgets = 0
    lock_func_counts = {'total': 0, 'types': {}, 'mutex_lock': {}}
    unlock_func_counts = {'total': 0, 'types': {}, 'mutex_unlock': {}}

    for root, _, files in os.walk(directory):
        for filename in files:
            if filename.endswith('.txt'):  # Assuming files have .txt extension
                file_path = os.path.join(root, filename)
                with open(file_path, 'r') as file:
                    for line in file:
                        total_gadgets += extract_gadgets(line)
                        
                        lock_func = extract_lock_func(line)
                        if lock_func:
                            lock_func_counts['total'] += 1
                            if lock_func in lock_func_counts['types']:
                                lock_func_counts['types'][lock_func] += 1
                            else:
                                lock_func_counts['types'][lock_func] = 1
                            if 'mutex_lock' in lock_func:
                                if lock_func in lock_func_counts['mutex_lock']:
                                    lock_func_counts['mutex_lock'][lock_func] += 1
                                else:
                                    lock_func_counts['mutex_lock'][lock_func] = 1

                        unlock_func = extract_unlock_func(line)
                        if unlock_func:
                            unlock_func_counts['total'] += 1
                            if unlock_func in unlock_func_counts['types']:
                                unlock_func_counts['types'][unlock_func] += 1
                            else:
                                unlock_func_counts['types'][unlock_func] = 1
                            if 'mutex_unlock' in unlock_func:
                                if unlock_func in unlock_func_counts['mutex_unlock']:
                                    unlock_func_counts['mutex_unlock'][unlock_func] += 1
                                else:
                                    unlock_func_counts['mutex_unlock'][unlock_func] = 1

    return total_gadgets, lock_func_counts, unlock_func_counts

if __name__ == '__main__':
    file_count = count_files(ll_dir)

    while True:
        status = run_task()
        processed_files = count_files(txt_dir)
        print_loading_bar(processed_files, file_count)
        if status == 0:
            print("\nAll files have been processed successfully.")
            break
        time.sleep(0.2)  # Delay before rerunning

    # Calculate the total number of SCUAF gadgets and lock function counts
    total_gadgets, lock_func_counts, unlock_func_counts = process_files(txt_dir)

    # Prepare the data to be saved
    data = {
        'linux_version': linux_version,
        'bc_dir': bc_dir,
        'll_dir': ll_dir,
        'txt_dir': txt_dir,
        'file_count': file_count, 
        'scuaf_gadgets': total_gadgets,
        'lock_func_counts': lock_func_counts,
        'unlock_func_counts': unlock_func_counts
    }

    # Save the data to a JSON file
    with open(stats_dir, 'w') as f:
        json.dump(data, f, indent=4)

    print(f'Total SCUAF gadgets found: {total_gadgets}')
    print(f'Lock function counts: {lock_func_counts}')
    print(f'Unlock function counts: {unlock_func_counts}')
