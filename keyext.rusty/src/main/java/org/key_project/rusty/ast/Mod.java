package org.key_project.rusty.ast;

import org.jspecify.annotations.NonNull;
import org.key_project.logic.SyntaxElement;
import org.key_project.rusty.ast.visitor.Visitor;
import org.key_project.util.collection.ImmutableList;

import java.util.Objects;
import java.util.stream.Collectors;

public class Mod implements RustyProgramElement{
    private final ImmutableList<Item> items;

    public Mod(ImmutableList<Item> items) {
        this.items = items;
    }

    @Override
    public int getChildCount() {
        return items.size();
    }

    @Override
    public @NonNull SyntaxElement getChild(int n) {
        return Objects.requireNonNull(items.get(n));
    }

    @Override
    public String toString() {
        return items.map(Item::toString).stream().collect(Collectors.joining("\n"));
    }

    @Override
    public void visit(Visitor v) {
        throw new RuntimeException("Shouldn't be called");
    }
}
