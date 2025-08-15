/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.key.api.doc;

import java.util.List;

import org.jspecify.annotations.NullMarked;

/// Metamodel of the API. This class contains classes which represents the functionality and
/// interfaces of the API.
///
/// @author Alexander Weigl
/// @version 1 (29.10.23)
@NullMarked
public class Metamodel {

    /// Root class of the metamodel.
    ///
    /// @param endpoints a list of provided services
    /// @param types a list of known types
    public record KeyApi(
            List<Endpoint> endpoints,
            List<Type> types) {
    }

    /// An {@link Endpoint} is a provided service/method.
    sealed interface Endpoint {
        /// complete name of the service
        String name();

        /// a markdown documentation
        String documentation();

        default String kind() {
            return getClass().getName();
        }

        /// a list of its arguments
        List<Argument> args();
    }

    /// A [Argument] of an endpoint
    ///
    /// @param name the argument name
    /// @param type the argument type
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

    ///
    public record ServerNotification(String name, String documentation, List<Argument> args)
            implements Endpoint {
    }

    ///
    public record ClientRequest(String name, String documentation, List<Argument> args,
            Type returnType)
            implements Endpoint {
    }

    ///
    public record ClientNotification(String name, String documentation, List<Argument> args)
            implements Endpoint {
    }

    ///
    public record Field(String name, /* Type */ String type, String documentation) {
        Field(String name, String type) {
            this(name, type, "");
        }
    }

    /// A data type
    public sealed interface Type {
        default String kind() {
            return getClass().getName();
        }

        /// Documentation of the data type
        String documentation();

        /// name of the data type
        String name();

        ///
        String identifier();
    }


    /// Typical built-in data types supported by the API
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

    /// A data type representing that a method returns or expecting either type `a` or `b`.
    ///
    /// @param a
    /// @param b
    /// @param documentation
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
    public record EnumType(String typeName, String typeFullName, List<String> values,
            String documentation) implements Type {

        @Override
        public String name() {
            return typeName;
        }

        public String identifier() {
            return typeFullName;
        }
    }
}
