/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.smt.newsmt2;

import java.util.Map;

import de.uka.ilkd.key.java.Services;

/**
 * SMT handler properties are properties for the new modular smt handler.
 *
 * They can defined individually in each {@link SMTHandler}. The settings dialog (etc.) probe the
 * installed SMTHandlers for all available properties.
 *
 * SMT handler properties have a limited system for type safety to avoid nasty exceptions.
 *
 * @param <T> type of the stored data.
 *
 * @author Mattias Ulbrich
 */
public abstract class SMTHandlerProperty<T> {

    /**
     * Name of the property. Should not have spaces. This is also used in the .props files for
     * properties.
     */
    private final String identifier;

    /**
     * The text to be used in the settings dialog as label.
     */
    private final String label;

    /**
     * The tooltip to be shown in the settings dialog.
     */
    private final String description;

    public SMTHandlerProperty(String identifier, String label, String description) {
        this.identifier = identifier;
        this.label = label;
        this.description = description;
    }

    /**
     * Verify that the given string value can be converted to a value of the stored data type
     *
     * @param value potential string representation of a property, not null.
     * @return true iff the argument is a valid representation.
     */
    public abstract boolean verify(String value);

    /**
     * Convert
     *
     * <p>
     * Precondition: {@code verify(s) == true}
     * </p>
     *
     * @param s String to parse into a value
     * @return the value represented by s.
     */
    public abstract T fromString(String s);

    /**
     * The default value for the stored data type in case there is no value stored
     *
     * @return a non-null constant value
     */
    public abstract T defaultValue();

    /*
     * Part of the Visitor pattern
     *
     * @see SMTHandlerPropertyVisitor
     */
    public abstract <A, R> R accept(SMTHandlerPropertyVisitor<A, R> visitor, A arg);

    public String getIdentifier() {
        return identifier;
    }

    public String getLabel() {
        return label;
    }

    public String getDescription() {
        return description;
    }

    /**
     * Extract a value of this property from a Services object.
     *
     * It uses the current proof (that must exist!), accesses its settings and there the new
     * smtsetting.
     *
     * @param services non-null services object
     * @return the value read from the services.
     */
    public T get(Services services) {
        String val = services.getProof().getSettings().getNewSMTSettings().get(getIdentifier());
        if (val == null) {
            return defaultValue();
        }
        return fromString(val);
    }

    /**
     * Extract a value of this property from a string property table.
     *
     * @param properties non-null map to look up the value
     * @return the value read from the table.
     */
    public T get(Map<String, Object> properties) {
        Object val = properties.get(getIdentifier());
        if (val == null) {
            return defaultValue();
        }
        return fromString(val.toString());
    }

    /**
     * A property of type String.
     *
     * Any value is allowed, no conversion needed, default is "".
     */
    public static class StringProperty extends SMTHandlerProperty<String> {

        public StringProperty(String identifier, String heading, String description) {
            super(identifier, heading, description);
        }

        @Override
        public boolean verify(String value) {
            return true;
        }

        @Override
        public String fromString(String s) {
            return s;
        }

        @Override
        public String defaultValue() {
            return "";
        }

        @Override
        public <A, R> R accept(SMTHandlerPropertyVisitor<A, R> visitor, A arg) {
            return visitor.visit(this, arg);
        }
    }

    /**
     * A property of type int.
     *
     * The string must be a parsable integer value in decimal representation in integer range.
     * Default value is 0.
     */
    public static class IntegerProperty extends SMTHandlerProperty<Integer> {

        private final int min;
        private final int max;

        public IntegerProperty(String identifier, String heading, String description, int min,
                int max) {
            super(identifier, heading, description);
            this.min = min;
            this.max = max;
        }

        @Override
        public boolean verify(String value) {
            try {
                int ival = Integer.parseInt(value);
                return min <= ival && ival <= max;
            } catch (NumberFormatException e) {
                return false;
            }
        }

        @Override
        public Integer fromString(String s) {
            return Integer.parseInt(s);
        }

        @Override
        public Integer defaultValue() {
            if (min <= 0 && 0 <= max) {
                return 0;
            } else {
                return min;
            }
        }

        public int getMinimum() {
            return min;
        }

        public int getMaximum() {
            return max;
        }

        @Override
        public <A, R> R accept(SMTHandlerPropertyVisitor<A, R> visitor, A arg) {
            return visitor.visit(this, arg);
        }
    }

    /**
     * A property of type boolean.
     *
     * The string must be a "true" or "false. Default value is "false".
     */
    public static class BooleanProperty extends SMTHandlerProperty<Boolean> {

        public BooleanProperty(String identifier, String heading, String description) {
            super(identifier, heading, description);
        }

        @Override
        public boolean verify(String value) {
            return value.equalsIgnoreCase("true") || value.equalsIgnoreCase("false");
        }

        @Override
        public Boolean fromString(String s) {
            return Boolean.valueOf(s);
        }

        @Override
        public Boolean defaultValue() {
            return Boolean.FALSE;
        }

        @Override
        public <A, R> R accept(SMTHandlerPropertyVisitor<A, R> visitor, A arg) {
            return visitor.visit(this, arg);
        }
    }

    /**
     * A property for an enum type. The allowed strings are the names of the enum constants of the
     * type. Default value is the first constant of E.
     *
     * @param <E> an enum class that is wrapped here. Must contain at least one constant.
     */
    public static class EnumProperty<E extends Enum<E>> extends SMTHandlerProperty<E> {
        private final Class<E> enumType;

        public EnumProperty(String identifier, String heading, String description,
                Class<E> enumType) {
            super(identifier, heading, description);
            this.enumType = enumType;
        }

        public E fromString(String value) {
            for (E enumConstant : enumType.getEnumConstants()) {
                if (value.equalsIgnoreCase(enumConstant.toString())) {
                    return enumConstant;
                }
            }
            return null;
        }

        @Override
        public boolean verify(String value) {
            return fromString(value) != null;
        }

        @Override
        public E defaultValue() {
            return enumType.getEnumConstants()[0];
        }

        public Class<E> getEnumType() {
            return enumType;
        }

        @Override
        public <A, R> R accept(SMTHandlerPropertyVisitor<A, R> visitor, A arg) {
            return visitor.visit(this, arg);
        }
    }

}
