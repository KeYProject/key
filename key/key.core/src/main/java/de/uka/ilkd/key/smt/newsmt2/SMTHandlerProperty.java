package de.uka.ilkd.key.smt.newsmt2;

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

    public abstract T get(Map<String, Object> properties);

    public abstract T defaultValue();

    public String getIdentifier() {
        return identifier;
    }

    public String getHeading() {
        return heading;
    }

    public String getDescription() {
        return description;
    }

    public static class StringProperty extends SMTHandlerProperty<String> {

        public StringProperty(String identifier, String heading, String description) {
            super(identifier, heading, description);
        }

        @Override
        public boolean verify(String value) {
            return false;
        }

        @Override
        public String get(Map<String, Object> properties) {
            Object val = properties.get(getIdentifier());
            if (val == null) {
                return defaultValue();
            }
            return val.toString();
        }

        @Override
        public String defaultValue() {
            return "";
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
        public Integer get(Map<String, Object> properties) {
            Object prop = properties.get(getIdentifier());
            if (prop == null) {
                return defaultValue();
            }
            return Integer.parseInt(prop.toString());
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
        public Boolean get(Map<String, Object> properties) {
            Object prop = properties.get(getIdentifier());
            if (prop == null) {
                return defaultValue();
            }
            return Boolean.parseBoolean(prop.toString());
        }

        @Override
        public Boolean defaultValue() {
            return Boolean.FALSE;
        }
    }

    public static class EnumProperty<E extends Enum<E>> extends SMTHandlerProperty<E> {
        private final Class<E> enumType;

        public EnumProperty(String identifier, String heading, String description, Class<E> enumType) {
            super(identifier, heading, description);
            this.enumType = enumType;
        }

        private E getConstant(String value) {
            for (E enumConstant : enumType.getEnumConstants()) {
                if(value.equalsIgnoreCase(enumConstant.toString())) {
                    return enumConstant;
                }
            }
            return null;
        }

        @Override
        public boolean verify(String value) {
            return getConstant(value) != null;
        }

        @Override
        public E get(Map<String, Object> properties) {
            Object prop = properties.get(getIdentifier());
            if (prop == null) {
                return defaultValue();
            }
            String val = prop.toString();
            return getConstant(val);
        }

        @Override
        public E defaultValue() {
            return enumType.getEnumConstants()[0];
        }
    }

}
