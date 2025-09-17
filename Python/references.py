import os
import re
from collections import defaultdict

# Regular expressions to match definitions, references, and comment markers
definition_pattern = re.compile(r'\b(Definition|Lemma|Theorem|Fixpoint|Inductive|Record)\s+(\w+)', re.MULTILINE)
reference_pattern = re.compile(r'\b(\w+)\b')
end_pattern = re.compile(r'\b(Qed|Defined|Admitted)\b', re.MULTILINE)
comment_start_pattern = re.compile(r'\(\*')
comment_end_pattern = re.compile(r'\*\)')

# Set of Coq keywords and tactics to exclude from dependencies
coq_keywords = {
    "intros", "reflexivity", "simpl", "rewrite", "apply", "unfold", "induction",
    "case", "clear", "split", "exists", "destruct", "assert", "intuition", "admit",
    "admitted", "fun", "match", "end", "with", "None", "Some", "if", "then", "else",
    "forall"
}

def collect_defined_names(project_path):
    defined_names = set()
    for root, _, files in os.walk(project_path):
        for file in files:
            if file.endswith('.v'):
                file_path = os.path.join(root, file)
                with open(file_path, 'r') as f:
                    content = f.read()
                    matches = definition_pattern.findall(content)
                    for match in matches:
                        defined_names.add(match[1])
    return defined_names

def parse_coq_file(file_path, defined_names):
    with open(file_path, 'r') as file:
        content = file.read()
    
    # Find all definitions in the file
    definitions = definition_pattern.findall(content)
    
    # Map to store dependencies
    dependencies = defaultdict(set)
    
    # Track current definition being processed
    current_definition = None
    inside_comment = False
    
    lines = content.splitlines()
    for line in lines:
        # Handle multi-line comments
        if inside_comment:
            if comment_end_pattern.search(line):
                inside_comment = False
            continue
        elif comment_start_pattern.search(line):
            if not comment_end_pattern.search(line):  # Comment continues on next line
                inside_comment = True
            continue

        # Check if the line starts a new definition
        match = definition_pattern.match(line)
        if match:
            current_definition = match.group(2)
            dependencies[current_definition] = set()
            continue

        # Check if the line ends a definition
        if end_pattern.search(line):
            current_definition = None
            continue
        
        # If within a definition, find references
        if current_definition:
            refs = reference_pattern.findall(line)
            for ref in refs:
                # Add to dependencies only if ref is in defined_names and not a Coq keyword
                if ref != current_definition and ref in defined_names and ref not in coq_keywords:
                    dependencies[current_definition].add(ref)
    
    return dependencies

def parse_coq_project(project_path):
    # Step 1: Collect all defined names
    defined_names = collect_defined_names(project_path)
    
    # Step 2: Parse files for dependencies
    all_dependencies = defaultdict(set)
    for root, _, files in os.walk(project_path):
        for file in files:
            if file.endswith('.v'):
                file_path = os.path.join(root, file)
                file_dependencies = parse_coq_file(file_path, defined_names)
                for key, refs in file_dependencies.items():
                    all_dependencies[key].update(refs)
    
    return all_dependencies

def write_dependencies(output_file, dependencies):
    all_nodes = sorted(dependencies.keys())
    
    with open(output_file, 'w') as file:
        # Write nodes with labels
        for node in all_nodes:
            file.write(f"{node} {node}\n")
        
        file.write("#\n")  # Separator for edges
        
        # Write edges
        for definition, refs in sorted(dependencies.items()):
            if refs:
                for ref in sorted(refs):
                    file.write(f"{definition} {ref}\n")

if __name__ == "__main__":
    project_path = os.path.join(os.path.dirname(__file__), '..')  # Relative path to project root
    output_file = 'references_output.tgf'
    
    dependencies = parse_coq_project(project_path)
    write_dependencies(output_file, dependencies)

    print(f"Dependencies written to {output_file}")
