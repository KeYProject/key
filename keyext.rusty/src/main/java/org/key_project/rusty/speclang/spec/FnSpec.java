package org.key_project.rusty.speclang.spec;

import org.key_project.rusty.parser.hir.DefId;

public record FnSpec(DefId target, SpecCase[] cases) {
}
