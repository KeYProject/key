package de.uka.ilkd.key.smt.newsmt2;

import de.uka.ilkd.key.java.Services;

import java.util.Map;

public abstract class SMTHandlerProperty<T> {

    private final String identifier;
    private final String heading;
    private final String description;

    public SMTHandlerProperty(String identifier, String heading,
                              String description) {
        this.identifier = identifier;
        this.heading = heading;
        this.description = description;
    }

    public abstract boolean verify(String value);

    public abstract T fromString(String s);

    public abstract T defaultValue();

    public abstract <A,R> R accept(SMTHandlerPropertyVisitor<A, R> visitor, A arg);

    public T get(Map<String, Object> properties) {
        Object val = properties.get(getIdentifier());
        if (val == null) {
            return defaultValue();
        }
        return fromString(val.toString());
    }

    public String getIdentifier() {
        return identifier;
    }

    public String getHeading() {
        return heading;
    }

    public String getDescription() {
        return description;
    }

    public T get(Services services) {
        String val = services.getProof().getSettings().getNewSMTSettings().get(getIdentifier());
        if (val == null) {
            return defaultValue();
        }
        return fromString(val);
    }

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

    public static class IntegerProperty extends SMTHandlerProperty<Integer> {

        private final int min;
        private final int max;

        public IntegerProperty(String identifier, String heading, String description, int min, int max) {
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
            if(min <= 0 && 0 <= max) {
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

    public static class BooleanProperty extends SMTHandlerProperty<Boolean> {

        public BooleanProperty(String identifier, String heading, String description) {
            super(identifier, heading, description);
        }

        @Override
        public boolean verify(String value) {
            return value.equalsIgnoreCase("true") ||
                    value.equalsIgnoreCase("false");
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

    public static class EnumProperty<E extends Enum<E>> extends SMTHandlerProperty<E> {
        private final Class<E> enumType;

        public EnumProperty(String identifier, String heading, String description, Class<E> enumType) {
            super(identifier, heading, description);
            this.enumType = enumType;
        }

        public E fromString(String value) {
            for (E enumConstant : enumType.getEnumConstants()) {
                if(value.equalsIgnoreCase(enumConstant.toString())) {
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
