/*
 * Copyright (C) 2010 Universitaet Karlsruhe, Germany
 *    written by Mattias Ulbrich
 * 
 * The system is protected by the GNU General Public License. 
 * See LICENSE.TXT for details.
 */
package edu.kit.kastel.formal.mixfix;


/**
 * Simple sample implementation 
 */
public class SyntaxRule extends SequenceRule<String, String> {

    private String name;
    private String description;

    public SyntaxRule(String name, String description, int left, int right) {
        super(decompose(description), left, right);
        this.name = name;
        this.description = description;
    }

    private static class EqMatcher implements Matcher<String> {
        String expect;

        public EqMatcher(String string) {
            expect = string;
        }

        @Override
        public boolean matches(String t) {
            return expect.equals(t);
        }
    }

    private static Matcher<String>[] decompose(String description) {
        String[] parts = description.split(" +");
        EqMatcher[] result = new EqMatcher[parts.length];
        for (int i = 0; i < parts.length; i++) {
            if (!"_".equals(parts[i])) {
                result[i] = new EqMatcher(parts[i]);
            }
        }
        return result;
    }

    @Override
    protected String makeResult(ADTList<String> parameters) {
        return name + parameters;
    }
    
    @Override
    public String toString() {
        return name + " - " + description;
    }

}
