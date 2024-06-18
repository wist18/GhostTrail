import os
import re

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

# Directory containing the files
directory = 'passes-out'

# Output file
output_file = 'stats.txt'

# Calculate the total number of SCUAF gadgets
total_gadgets = sum_scuaf_gadgets(directory)

# Write the total to the output file
write_total_to_file(total_gadgets, output_file)

print(f'Total SCUAF gadgets found: {total_gadgets}')
