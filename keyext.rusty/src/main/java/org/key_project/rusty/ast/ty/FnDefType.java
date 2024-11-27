package org.key_project.rusty.ast.ty;

import org.jspecify.annotations.NonNull;
import org.key_project.logic.Name;
import org.key_project.logic.sort.Sort;
import org.key_project.rusty.Services;
import org.key_project.rusty.ast.abstraction.Type;
import org.key_project.rusty.ast.fn.Function;

public record FnDefType(Function fn) implements Type {
    @Override
    public Sort getSort(Services services) {
        return null;
    }

    @Override
    public RustType toRustType(Services services) {
        return null;
    }

    @Override
    public @NonNull Name name() {
        return fn.name();
    }
}
