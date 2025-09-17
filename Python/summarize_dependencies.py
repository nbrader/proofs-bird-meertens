#!/usr/bin/env python3

import pexpect
import re
import os

def get_coq_dependencies(coq_script):
    # Start coqtop with the correct include paths
    coqtop_command = 'coqtop -Q ../Coq/BirdMeertens BirdMeertens -Q ../Coq/FreeMonoid FreeMonoid'
    child = pexpect.spawn(coqtop_command)
    child.expect(r'Coq <')
    
    with open(coq_script, 'r') as f:
        commands = f.readlines()
    
    output = ""
    for command in commands:
        child.sendline(command.strip())
        child.expect(r'Coq <', timeout=60)
        output += child.before.decode('utf-8')
    
    child.terminate()
    return output

def parse_dependencies(output):
    # Patterns to capture the theorems and their dependencies
    theorem_pattern = re.compile(r'Print Assumptions ([\w\.]+)\.')
    dependencies_pattern = re.compile(r'(Axioms|Hypotheses|Assumptions|Variables|Dependencies):([\s\S]+?)(?=\n\n|\Z)')
    
    # Find all theorems
    theorems = theorem_pattern.findall(output)
    
    # Split output into sections for each theorem
    sections = output.split("Print Assumptions ")[1:]  # Split by "Print Assumptions " and ignore the first empty part
    
    dependency_dict = {}
    for theorem, section in zip(theorems, sections):
        # Find all dependencies in the section
        dependencies = dependencies_pattern.findall(section)
        deps_list = []
        for deps in dependencies:
            deps = deps[1].strip().split('\n')
            deps = [dep.strip() for dep in deps if dep.strip()]
            deps_list.extend(deps)
        dependency_dict[theorem] = deps_list
    
    return dependency_dict

if __name__ == '__main__':
    coq_script = os.path.join('..', 'Coq', 'BirdMeertens', 'dependencies.v')
    output = get_coq_dependencies(coq_script)
    dependencies = parse_dependencies(output)
    
    for theorem, deps in dependencies.items():
        print(f"{theorem} depends on:\n")
        for dep in deps:
            if dep.startswith(':') or dep.startswith('(') or dep.startswith('{') or dep.startswith('['):
                print(f"    {dep}")
            else:
                print(f"{dep}")
        print("\n" + "="*50 + "\n")  # Add a clear separation between lemmas
