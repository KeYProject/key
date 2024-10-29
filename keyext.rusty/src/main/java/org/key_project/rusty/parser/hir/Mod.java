package org.key_project.rusty.parser.hir;

import org.key_project.rusty.parser.hir.item.Item;

public record Mod(ModSpans spans, Item[] items) {
    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append("mod@");sb.append(spans).append("{");
        for (Item item : items) {sb.append(item).append(",");}
        sb.append("}");
        return sb.toString();
    }
}
