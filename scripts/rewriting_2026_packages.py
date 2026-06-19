#!/usr/bin/env python3

from pathlib import Path
import shutil
import re


def refactor_java_package(subfolder: str, old_package: str, new_package: str) -> None:
    """
    Move Java files from old_package to new_package under every source root matching:

        **/src/*/java/**

    Then rewrite:
      - package declarations
      - imports referencing the old package

    Example:
        refactor_java_package(
            "my-project",
            "com.example.oldpkg",
            "com.example.newpkg",
        )
    """

    base = Path(subfolder).resolve()

    old_dir = base / Path(*old_package.split("."))
    new_dir = base / Path(*new_package.split("."))

    source_roots = [p for p in base.glob("**/src/*/java") if p.is_dir()]

    if not source_roots:
        raise RuntimeError(f"No Java source roots found under {base}")

    moved_files: list[Path] = []

    if not old_dir.exists():
        return

    new_dir.mkdir(parents=True, exist_ok=True)

    # Move everything under the old package directory.
    for item in old_dir.iterdir():
        destination = new_dir / item.name
        if destination.exists():
            raise FileExistsError(
                f"Cannot move {item} to {destination}: destination already exists"
            )

        shutil.move(str(item), str(destination))

        if destination.is_file() and destination.suffix == ".java":
            moved_files.append(destination)
        elif destination.is_dir():
            moved_files.extend(destination.rglob("*.java"))

        _remove_empty_parents(old_dir, stop_at=source_root)

    # Rewrite all Java files under every source root.
    # This updates imports in files that reference the moved package.
    for source_root in source_roots:
        for java_file in source_root.rglob("*.java"):
            _rewrite_java_file(java_file, old_package, new_package)

    print(f"Moved {len(moved_files)} Java files from {old_package} to {new_package}")


def _rewrite_java_file(java_file: Path, old_package: str, new_package: str) -> None:
    text = java_file.read_text(encoding="utf-8")
    original = text

    # Rewrite package declarations:
    #
    #   package com.example.oldpkg;
    #   package com.example.oldpkg.sub;
    #
    # becomes:
    #
    #   package com.example.newpkg;
    #   package com.example.newpkg.sub;
    package_pattern = re.compile(
        rf"^(\s*package\s+){re.escape(old_package)}(\b(?:\.[A-Za-z_][A-Za-z0-9_]*)*\s*;)",
        re.MULTILINE,
    )

    text = package_pattern.sub(
        rf"\1{new_package}\2",
        text,
    )

    # Rewrite imports:
    #
    #   import com.example.oldpkg.Foo;
    #   import static com.example.oldpkg.Foo.bar;
    #   import com.example.oldpkg.sub.Foo;
    #
    # becomes:
    #
    #   import com.example.newpkg.Foo;
    #   import static com.example.newpkg.Foo.bar;
    #   import com.example.newpkg.sub.Foo;
    import_pattern = re.compile(
        rf"^(\s*import\s+(?:static\s+)?){re.escape(old_package)}(\b(?:\.[A-Za-z_][A-Za-z0-9_]*)*(?:\.\*)?\s*;)",
        re.MULTILINE,
    )

    text = import_pattern.sub(
        rf"\1{new_package}\2",
        text,
    )

    if text != original:
        java_file.write_text(text, encoding="utf-8")


def _remove_empty_parents(path: Path, stop_at: Path) -> None:
    """
    Remove empty directories from path upwards until stop_at.
    Does not remove stop_at.
    """
    path = path.resolve()
    stop_at = stop_at.resolve()

    while path != stop_at and stop_at in path.parents:
        try:
            path.rmdir()
        except OSError:
            break

        path = path.parent


if __name__ == "__main__":
    refactor_java_package("key.core.example", "org.key_project", "org.key_project.example")    
    refactor_java_package("key.ui", "de.uka.ilkd.key.core", "de.uka.ilkd.key.ui.core")
    refactor_java_package("key.ui", "de.uka.ilkd.key.gui", "de.uka.ilkd.key.ui.gui")
    refactor_java_package("key.ui",  "de.uka.ilkd.key.proof", "de.uka.ilkd.key.ui.proof")
    refactor_java_package("key.ui",  "de.uka.ilkd.key.proof.mgt", "de.uka.ilkd.key.ui.proof.mgt")
    refactor_java_package("key.ui",  "de.uka.ilkd.key.util", "de.uka.ilkd.key.ui.util")
    refactor_java_package("keyext.caching", "org.key_project.reference", "org.key_project.caching")