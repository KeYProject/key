package de.uka.ilkd.key.parser;

import de.uka.ilkd.key.logic.sort.Sort;


public class IdDeclaration {

    private String name;
    private Sort sort;

    public IdDeclaration(String p_name, Sort p_sort) {
        name = p_name;
        sort = p_sort;
    }

    public String getName() {
        return name;
    }

    public Sort getSort() {
        return sort;
    }

}
