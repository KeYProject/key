package de.uka.ilkd.key.nparser;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.GenericSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.logic.sort.SortImpl;
import org.key_project.util.collection.ImmutableArray;

import java.util.LinkedList;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * @author Alexander Weigl
 * @version 1 (17.10.19)
 */
public class NamespaceBuilder {
    private NamespaceSet nss;
    private Pattern FUNCTION = Pattern.compile("(.+) (.+?) ?\\((?:(.+?)(?:, (.+?))*)?\\)");

    public NamespaceBuilder() {
        this(new NamespaceSet());
    }

    public NamespaceBuilder(NamespaceSet nss) {
        this.nss = nss;
    }

    public NamespaceBuilder addSort(String name) {
        nss.sorts().add(new SortImpl(new Name(name)));
        return this;
    }

    public NamespaceBuilder addFunction(String expr) {
        Matcher matcher = FUNCTION.matcher(expr);
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

            Function f = new Function(new Name(name), sort, args.toArray(new Sort[] {}));
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

    public NamespaceBuilder addVariable(String name, String sort) {
        nss.variables().add(new LogicVariable(new Name(name), getOrCreateSort(sort)));
        return this;
    }

    public NamespaceBuilder addPredicate(String s) {
        s = "bool " + s;
        return addFunction(s);
    }

    public NamespaceBuilder addProgramVariable(String sort, String varName) {
        Sort s = getOrCreateSort(sort);
        ProgramVariable pv = new LocationVariable(new ProgramElementName(varName), s);
        nss.programVariables().add(pv);
        return this;
    }
}
