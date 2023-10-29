package org.keyproject.key.api.data;

import de.uka.ilkd.key.logic.sort.Sort;

import java.util.List;

/**
 * @author Alexander Weigl
 * @version 1 (13.10.23)
 */
public record SortDesc(String string, String documentation,
                       List<SortDesc> extendsSorts,
                       boolean anAbstract, String s) {
    public static SortDesc from(Sort sort) {
        return new SortDesc(sort.name().toString(), sort.getDocumentation(),
                sort.extendsSorts().stream().map(SortDesc::from).toList(),
                sort.isAbstract(), sort.declarationString());
    }
}
