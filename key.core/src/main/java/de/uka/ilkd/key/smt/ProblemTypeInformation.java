/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.smt;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.Field;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.ClassDeclaration;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.smt.lang.SMTSort;
import de.uka.ilkd.key.smt.lang.SMTTermNumber;
import de.uka.ilkd.key.smt.lang.Util;

public class ProblemTypeInformation {

    Services services;

    final Map<String, SMTSort> fieldTypes;
    final Map<String, SMTSort> constantsTypes;
    final Map<String, Sort> originalConstantType;

    Set<Sort> javaSorts;

    private SMTSettings settings;

    private Map<SMTSort, SMTTermNumber> sortNumbers;

    private Map<String, SMTSort> sorts;

    public ProblemTypeInformation(TermServices services) {
        super();
        fieldTypes = new HashMap<>();
        constantsTypes = new HashMap<>();
        javaSorts = new HashSet<>();
        originalConstantType = new HashMap<>();
    }

    public void putOriginalConstantType(String c, Sort s) {
        originalConstantType.put(c, s);
    }

    public Sort getOriginalConstantType(String c) {
        return originalConstantType.get(c);
    }

    /**
     * @param key
     * @return
     * @see java.util.Map#get(java.lang.Object)
     */
    public SMTSort getTypeForConstant(Object key) {
        return constantsTypes.get(key);
    }

    /**
     * @param key
     * @param value
     * @return
     * @see java.util.Map#put(java.lang.Object, java.lang.Object)
     */
    public SMTSort putConstantType(String key, SMTSort value) {
        return constantsTypes.put(key, value);
    }



    public Set<Sort> getJavaSorts() {
        return javaSorts;
    }

    public void setJavaSorts(Set<Sort> javaSorts) {
        this.javaSorts = javaSorts;

    }

    /**
     * @param key
     * @return
     * @see java.util.Map#get(java.lang.Object)
     */
    public SMTSort getTypeForField(Object key) {
        return fieldTypes.get(key);
    }

    /**
     * @param key
     * @param value
     * @return
     * @see java.util.Map#put(java.lang.Object, java.lang.Object)
     */
    public SMTSort putFieldType(String key, SMTSort value) {

        return fieldTypes.put(key, value);
    }

    public Set<String> getFieldsForSort(String name) {
        JavaInfo info = services.getJavaInfo();
        Sort s = info.getKeYJavaType(name).getSort();
        return getFieldsForSort(s);
    }

    /**
     * Return a list of field names for the specified sort.
     *
     * @param s
     * @return
     */
    public Set<String> getFieldsForSort(Sort s) {
        Set<String> result = new HashSet<>();
        result.add(Util.processName("java.lang.Object::<created>"));

        JavaInfo info = services.getJavaInfo();

        KeYJavaType kjt = info.getKeYJavaType(s);

        if (kjt != null && kjt.getJavaType() instanceof ClassDeclaration) {
            ClassDeclaration c = (ClassDeclaration) kjt.getJavaType();

            for (KeYJavaType sp : info.getAllSupertypes(kjt)) {
                if (!sp.equals(kjt)) {
                    result.addAll(getFieldsForSort(sp.getSort()));
                }
            }

            for (Field f : info.getAllFields(c)) {

                String name = f.getFullName();
                // name = name.replace("::", "::$");
                name = Util.processName(name);
                result.add(name);

            }



        }


        return result;
    }

    public TermServices getServices() {
        return services;
    }

    public void setServices(Services services) {
        this.services = services;
    }

    public void setSettings(SMTSettings settings) {
        this.settings = settings;

    }

    public void setSortNumbers(Map<SMTSort, SMTTermNumber> sortNumbers) {
        this.sortNumbers = sortNumbers;

    }

    public SMTSettings getSettings() {
        return settings;
    }

    public String getPrefixForSort(SMTSort sort) {
        SMTTermNumber n = sortNumbers.get(sort);

        long val = n.getIntValue();

        StringBuilder s = new StringBuilder(Long.toBinaryString(val));

        while (s.length() < 3) {
            s.insert(0, "0");
        }

        return s.toString();


    }

    public void setSorts(Map<String, SMTSort> sorts) {
        this.sorts = sorts;
    }

    public SMTSort getSort(String sortName) {
        return sorts.get(sortName);
    }



}
