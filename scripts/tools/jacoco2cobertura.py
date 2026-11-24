#!/usr/bin/env python3
"""Convert a JaCoCo XML report into a Cobertura XML report.

GitHub's code coverage ingestion expects Cobertura XML and only uses line
coverage. This converter therefore emits one ``<class>`` element per source
file: JaCoCo describes each source file once under ``<package>`` but repeats
the same lines for every class declared in it, which bloats a repository-wide
report by more than an order of magnitude.

Usage::

    jacoco2cobertura.py JACOCO_XML COBERTURA_XML [SOURCE_ROOT ...]

Source roots are relative to the repository root. A source file is emitted
with its repository-relative path; source files that no source root contains
(for example generated sources) are skipped, because they cannot be matched
to files in the repository.
"""

import os
import sys
import time
import xml.etree.ElementTree as ET


def source_file_path(package, name, source_roots):
    """Return the repository-relative path of a JaCoCo source file, or None."""
    relative = os.path.join(package, name.lstrip("/"))
    for root in source_roots:
        candidate = os.path.normpath(os.path.join(root, relative))
        if os.path.isfile(candidate):
            return candidate.replace(os.sep, "/")
    return None


def line_hits(jacoco_line):
    """Return 1 if the line was executed, 0 otherwise."""
    return "1" if int(jacoco_line.attrib["ci"]) > 0 else "0"


def convert(jacoco_xml, cobertura_xml, source_roots):
    """Write the Cobertura report and print the number of emitted files."""
    tree = ET.parse(jacoco_xml)
    root = tree.getroot()

    packages = []
    skipped = 0
    covered_lines = 0
    total_lines = 0

    for jacoco_package in root.findall("package"):
        package_name = jacoco_package.attrib["name"].replace("/", ".")
        classes = []

        for source_file in sorted(jacoco_package.findall("sourcefile"),
                                  key=lambda element: element.attrib["name"]):
            path = source_file_path(jacoco_package.attrib["name"],
                                    source_file.attrib["name"], source_roots)
            if path is None:
                skipped += 1
                continue

            lines = source_file.findall("line")
            if not lines:
                skipped += 1
                continue

            hits = [line_hits(line) for line in lines]
            file_covered = hits.count("1")
            covered_lines += file_covered
            total_lines += len(hits)

            class_name = os.path.splitext(os.path.basename(path))[0]
            qualified_name = package_name + "." + class_name if package_name else class_name
            classes.append((qualified_name, path, lines, hits, file_covered))

        if classes:
            packages.append((package_name, classes))

    coverage = ET.Element("coverage")
    coverage.set("line-rate", str(covered_lines / total_lines if total_lines else 0.0))
    coverage.set("branch-rate", "0.0")
    coverage.set("version", "jacoco2cobertura")
    coverage.set("timestamp", str(int(time.time())))

    sources = ET.SubElement(coverage, "sources")
    ET.SubElement(sources, "source").text = "."

    packages_element = ET.SubElement(coverage, "packages")
    for package_name, classes in packages:
        package_covered = sum(entry[4] for entry in classes)
        package_total = sum(len(entry[3]) for entry in classes)
        package = ET.SubElement(packages_element, "package")
        package.set("name", package_name)
        package.set("line-rate", str(package_covered / package_total if package_total else 0.0))
        package.set("branch-rate", "0.0")

        classes_element = ET.SubElement(package, "classes")
        for qualified_name, path, lines, hits, file_covered in classes:
            cls = ET.SubElement(classes_element, "class")
            cls.set("name", qualified_name)
            cls.set("filename", path)
            cls.set("line-rate", str(file_covered / len(lines)))
            cls.set("branch-rate", "0.0")
            ET.SubElement(cls, "methods")

            lines_element = ET.SubElement(cls, "lines")
            for jacoco_line, hit in zip(lines, hits):
                line = ET.SubElement(lines_element, "line")
                line.set("number", jacoco_line.attrib["nr"])
                line.set("hits", hit)

    ET.ElementTree(coverage).write(cobertura_xml, encoding="UTF-8", xml_declaration=True)
    return len(packages), sum(len(classes) for _, classes in packages), skipped, covered_lines, total_lines


def main(argv):
    if len(argv) < 3:
        print("Usage: jacoco2cobertura.py JACOCO_XML COBERTURA_XML [SOURCE_ROOT ...]",
              file=sys.stderr)
        return 1

    source_roots = argv[3:] or ["."]
    packages, files, skipped, covered, total = convert(argv[1], argv[2], source_roots)
    print("jacoco2cobertura: %d packages, %d files, %d skipped, %d/%d lines covered"
          % (packages, files, skipped, covered, total), file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
