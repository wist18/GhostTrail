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

# Create the directory path
bc_dir= f"linux-{linux_version}-bc"

# Create the directory path
ll_dir = f"linux-{linux_version}-ll"

# Directory containing the files
txt_dir = 'passes-out'

# Output file
stats_dir = 'stats.json'

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

# Function to process all files in a directory and subdirectories to sum up the SCUAF gadgets
def sum_scuaf_gadgets(directory):
    total_gadgets = 0

    for root, _, files in os.walk(directory):
        for filename in files:
            if filename.endswith('.txt'):  # Assuming files have .txt extension
                file_path = os.path.join(root, filename)
                with open(file_path, 'r') as file:
                    for line in file:
                        total_gadgets += extract_gadgets(line)
    
    return total_gadgets

# Function to write the total number of SCUAF gadgets to a file
def write_total_to_file(total, output_file):
    with open(output_file, 'w') as file:
        file.write(f'Total SCUAF gadgets found: {total}\n')

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

    # Calculate the total number of SCUAF gadgets
    total_gadgets = sum_scuaf_gadgets(txt_dir)

    # Prepare the data to be saved
    data = {
        'linux_version': linux_version,
        'bc_dir': bc_dir,
        'll_dir': ll_dir,
        'txt_dir': txt_dir,
        'file_count': file_count, 
        'scuaf_gadgets': total_gadgets
    }

    # Save the data to a JSON file
    with open(stats_dir, 'w') as f:
        json.dump(data, f, indent=4)

    print(f'Total SCUAF gadgets found: {total_gadgets}')