package de.uka.ilkd.key.nparser;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.sort.GenericSort;
import de.uka.ilkd.key.logic.sort.Sort;

import java.util.LinkedList;
import java.util.List;
import java.util.regex.Pattern;

/**
 * @author Alexander Weigl
 * @version 1 (17.10.19)
 */
public class NamespaceBuilder {
    private NamespaceSet nss;
    private Pattern FUNCTION = Pattern.compile(
            "(.+) (.+?) ?\\((?:(.+?)(?:, (.+?))*)?\\)");

    public NamespaceBuilder() {
        this(new NamespaceSet());
    }

    public NamespaceBuilder(NamespaceSet nss) {
        this.nss = nss;
    }

    public NamespaceBuilder addSort(String name) {
        nss.sorts().add(new GenericSort(new Name(name)));
        return this;
    }

    public NamespaceBuilder addFunction(String expr) {
        var matcher = FUNCTION.matcher(expr);
        if (matcher.find()) {
            Sort sort = getOrCreateSort(matcher.group(1));
            String name = matcher.group(2);
            List<Sort> args = new LinkedList<>();
            try {
                for (int i = 3; i <= matcher.groupCount(); i++) {
                    if (matcher.group(i) != null) {
                        args.add(getOrCreateSort(matcher.group(i)));
                    }
                }
            } catch (IndexOutOfBoundsException e) {
            }

            Function f = new Function(new Name(name), sort, args.toArray(new Sort[]{}));
            nss.functions().add(f);
        }
        return this;
    }

    private Sort getOrCreateSort(String group) {
        if (nss.sorts().lookup(group) == null) {
            addSort(group);
        }
        return nss.sorts().lookup(group);
    }

}
