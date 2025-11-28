/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.key.api.doc;/*
                                     * This file is part of KeY - https://key-project.org
                                     * KeY is licensed under the GNU General Public License Version
                                     * 2
                                     * SPDX-License-Identifier: GPL-2.0-only
                                     */

import java.util.List;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * @author Alexander Weigl
 * @version 1 (29.10.23)
 */
@NullMarked
public class Metamodel {

    /// Root class of the metamodel.
    ///
    /// @param endpoints a list of provided services
    /// @param types a list of known types
    public record KeyApi(
            List<Endpoint> endpoints,
            java.util.Map<Class<?>, Type> types) {
    }

    sealed

    interface Endpoint {
        String name();

        String documentation();

        default String kind() {
            return getClass().getSimpleName();
        }

        List<Argument> args();
    }

    public record Argument(String name, String type) {
    }

    /// A {@link ServerRequest} is the caller to the callee expecting an answer.
    ///
    /// @param name
    /// @param args
    /// @param documentation
    /// @param returnType
    public record ServerRequest(String name, String documentation, List<Argument> args,
            Type returnType)
            implements Endpoint {
    }

    record ServerNotification(String name, String documentation, List<Argument> args)
            implements Endpoint {
    }

    ///
    public record ClientRequest(String name, String documentation, List<Argument> args,
            Type returnType)
            implements Endpoint {
    }

    record ClientNotification(String name, String documentation, List<Argument> args)
            implements Endpoint {
    }

    record Field(String name, /* Type */ String type, String documentation) {

        Field(String name, String type) {
            this(name, type, "");
        }
    }

    public sealed


    interface Type {
        default String kind() {
            return getClass().getName();
        }

        String documentation();

        String name();

        String identifier();
    }


    enum BuiltinType implements Type {
        INT, LONG, STRING, BOOL, DOUBLE;

        @Override
        public String documentation() {
            return "built-in data type";
        }

        public String identifier() {
            return name().toLowerCase();
        }

    }

    /// List of `type`.
    ///
    /// @param type the type of list elements
    /// @param documentation documentation of this data type
    record ListType(Type type, String documentation) implements Type {

        @Override
        public String name() {
            return type().name() + "[]";
        }

        public String identifier() {
            return type().identifier() + "[]";
        }

    }

    /// Data type of objects or struct or record.
    ///
    /// @param typeName short type name
    /// @param typeFullName fully-qualified type name
    /// @param fields list of fields
    /// @param documentation documentation of data type
    record ObjectType(String typeName, String typeFullName, List<Field> fields,
            String documentation) implements Type {

        @Override
        public String name() {
            return typeName;
        }

        public String identifier() {
            return typeFullName;
        }
    }

    public record EitherType(Type a, Type b, String documentation) implements Type {

        @Override
        public String name() {
            return "either<a,b>";
        }

        public String identifier() {
            return name();
        }

    }

    /// Enumeration data type
    ///
    /// @param typeName short name of the data type
    /// @param typeFullName fully-qualified name
    /// @param values possible values of the enum
    /// @param documentation documentation of the data type
    public record EnumType(String typeName, String typeFullName, List<EnumConstant> values,
            String documentation) implements Type {

        @Override
        public String name() {
            return typeName;
        }

        public String identifier() {
            return typeFullName;
        }

    }

    record EnumConstant(String value, @Nullable String documentation) {
    }

}
