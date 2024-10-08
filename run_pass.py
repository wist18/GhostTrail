import subprocess
import time
import os
import re
import json
import matplotlib.pyplot as plt
from collections import defaultdict
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
    'lock': ["spin_lock", "spin_trylock", "read_lock", "read_trylock", "write_lock", "write_trylock", "down_read", "down_write", "mutex_lock", "mutex_trylock", "down"],
    'unlock': ["spin_unlock", "read_unlock", "write_unlock", "up_read", "up_write", "mutex_unlock", "up"],
    'free': ["guarded_free", "guarded_free_null", "guarded_free_val", "guarded_free_list_del"],
    'use': ["fptr_copy", "fptr_call"]
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

# Function to extract the class of gadgets from a single line
def extract_report_class(line):
    report_class_match = re.search(r'\breport_class=(\w+)', line)
    report_class = report_class_match.group(1) if report_class_match else None

    return report_class

# Function to extract lock function types from a single line
def extract_lock_func(line, report_class):
    func_match = re.search(rf'\b{report_class}_func=(\w+)', line)
    nesting_level_match = re.search(r'nesting_level=(\d+)', line)
    
    func = func_match.group(1) if func_match else None
    nesting_level = int(nesting_level_match.group(1)) if nesting_level_match else None
    
    return func, nesting_level

# Function to extract unlock function types from a single line
def extract_unlock_func(line):
    lock_func_match = re.search(r'\bunlock_func=(\w+)', line)
    nesting_level_match = re.search(r'nesting_level=(\d+)', line)
    
    lock_func = lock_func_match.group(1) if lock_func_match else None
    nesting_level = int(nesting_level_match.group(1)) if nesting_level_match else None
    
    return lock_func, nesting_level

def update_func_counts(func_counts, func, patterns, nesting_level):
    if func:
        func_counts['total'] += 1

        if nesting_level in func_counts['nesting_level']:
            func_counts['nesting_level'][nesting_level] += 1
        else:
            func_counts['nesting_level'][nesting_level] = 1

        if func in func_counts['types']:
            func_counts['types'][func] += 1
        else:
            func_counts['types'][func] = 1

        for key in patterns:
            if key in func:
                func_counts[key]['total'] += 1
                if func in func_counts[key]['types']:
                    func_counts[key]['types'][func] += 1
                else:
                    func_counts[key]['types'][func] = 1

                if nesting_level in func_counts[key]['nesting_level']:
                    func_counts[key]['nesting_level'][nesting_level] += 1
                else:
                    func_counts[key]['nesting_level'][nesting_level] = 1
                break

# Function to process all files in a directory and subdirectories to sum up the SCUAF gadgets and lock/unlock function types
def process_files(directory):
    total_gadgets = 0
    lock_func_counts = {'total': 0, 'nesting_level': {}, 'types': {}}
    unlock_func_counts = {'total': 0, 'nesting_level': {}, 'types': {}}
    free_gadget_counts = {'total': 0, 'nesting_level': {}, 'types': {}}
    use_gadget_counts = {'total': 0, 'nesting_level': {}, 'types': {}}
    seen_lines = set()
    component_lock_counts = defaultdict(int)

    for val in patterns['lock']:
        lock_func_counts[val] = {'total': 0, 'nesting_level': {}, 'types': {}}

    for val in patterns['unlock']:
        unlock_func_counts[val] = {'total': 0, 'nesting_level': {}, 'types': {}}

    for val in patterns['free']:
        free_gadget_counts[val] = {'total': 0, 'nesting_level': {}, 'types': {}}

    for val in patterns['use']:
        use_gadget_counts[val] = {'total': 0, 'nesting_level': {}, 'types': {}}
        

    for root, _, files in os.walk(directory):
        for filename in files:
            if filename.endswith('.txt'):  # Assuming files have .txt extension
                file_path = os.path.join(root, filename)
                component = file_path.split('/')[1]  # Assumes linux-version/component/path/to/file
                with open(file_path, 'r') as file:
                    for line in file:
                        total_gadgets += extract_gadgets(line)
                        if line.startswith('[LOCK-INFO]'):
                            component_lock_counts[component] += 1

                        report_class = extract_report_class(line)

                        func, nesting_level = extract_lock_func(line, report_class)

                        if (report_class == "lock"):
                            update_func_counts(lock_func_counts, func, patterns[report_class], nesting_level)
                        elif (report_class == "unlock"):
                            update_func_counts(unlock_func_counts, func, patterns[report_class], nesting_level)
                        elif (report_class in patterns['free']):
                            if line in seen_lines:
                                continue  # Skip the line if it has been seen before
                            update_func_counts(free_gadget_counts, report_class, [report_class], nesting_level)
                        elif (report_class in patterns['use']):
                            if line in seen_lines:
                                continue  # Skip the line if it has been seen before
                            update_func_counts(use_gadget_counts, report_class, [report_class], nesting_level)

                        # Only keep track of seen lines to remove duplicates for SCUAF gadgets. Duplicates for locks and unlocks can exist, sicne a lock can have multiple unlcoks associated with it and vice-versa.
                        seen_lines.add(line)  # Mark the line as seen

    return total_gadgets, lock_func_counts, unlock_func_counts, free_gadget_counts, use_gadget_counts, component_lock_counts

def getStats(dict, key, values_list):
    dict[key] = {"total": 0, "nesting_level": {}}
    for value in values_list:
        dict[key]["total"] += dict[value]["total"]
        
        for nesting_level in dict[value]["nesting_level"]:
            if nesting_level in dict[key]["nesting_level"]:
                dict[key]["nesting_level"][nesting_level] += dict[value]["nesting_level"][nesting_level]
            else:
                dict[key]["nesting_level"][nesting_level] = dict[value]["nesting_level"][nesting_level]


if __name__ == '__main__':
    file_count = min(count_files(ll_dir), count_files(bc_dir))

    while True:
        status = run_task()
        processed_files = count_files(txt_dir)
        print_loading_bar(processed_files, file_count)
        
        if status == 0:
            print("\nAll files have been processed successfully.")
            break

    # Calculate the total number of SCUAF gadgets and lock function counts
    total_gadgets, lock_func_counts, unlock_func_counts, free_gadget_counts, use_gadget_counts, component_lock_counts = process_files(txt_dir)
    getStats(lock_func_counts, "mutex_count", ["mutex_lock", "mutex_trylock"])
    getStats(lock_func_counts, "spin_lock_count", ["spin_lock", "spin_trylock"])
    getStats(lock_func_counts, "rw_spin_lock_count", ["read_lock", "read_trylock", "write_lock", "write_trylock"])
    getStats(lock_func_counts, "semaphore_count", ["down"])
    getStats(lock_func_counts, "rw_semaphore_count", ["down_read", "down_write"])
    # Prepare the data to be saved
    data = {
        'linux_version': linux_version,
        'bc_dir': bc_dir,
        'll_dir': ll_dir,
        'txt_dir': txt_dir,
        'file_count': file_count, 
        'scuaf_gadgets': total_gadgets,
        'lock_func_counts': lock_func_counts,
        'unlock_func_counts': unlock_func_counts,
        'free_gadgets': free_gadget_counts,
        'use_gadgets': use_gadget_counts,
        'component_lock_counts': component_lock_counts
    }

    # Save the data to a JSON file
    with open(stats_dir, 'w') as f:
        json.dump(data, f, indent=4)

    print(f'Total SCUAF gadgets found: {total_gadgets}')

    # Sort the components by number of locks in descending order
    sorted_component_lock_counts = dict(sorted(component_lock_counts.items(), key=lambda item: item[1], reverse=True))

    # Plot the number of locks for each Linux component
    components = list(sorted_component_lock_counts.keys())
    counts = list(sorted_component_lock_counts.values())

    plt.figure(figsize=(9, 6))
    bars = plt.barh(components, counts, color='blue')
    plt.ylabel('Linux Component', fontsize=12)
    plt.xlabel('Number of SRCs', fontsize=12)
    #plt.title('Number of SRCs per Linux Component', fontsize=14)
    plt.yticks(rotation=0, fontsize=10)
    plt.xticks(fontsize=10)

    # Add value labels on the bars with adjusted font size
    for bar in bars:
        width = bar.get_width()
        plt.text(width, bar.get_y() + bar.get_height() / 2.0, f'{width}', ha='left', va='center', fontsize=10)

    plt.tight_layout()
    plt.savefig('src_per_component.png')
    plt.show()