/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.key.api.doc;

import java.util.List;
import java.util.Map;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import org.keyproject.key.api.data.DataExamples;

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
            java.util.Map<Class<?>, Type> types,
            Map<String, HelpText> segmentDocumentation) {
    }

    /// Javadoc texts
    public record HelpText(String text, List<HelpTextEntry> others) {
    }

    /// Javadoc categories
    public record HelpTextEntry(String name, String value) {
    }


    /// An {@link Endpoint} is a provided service/method.
    public sealed interface Endpoint {
        /// complete name of the service
        String name();

        /// a markdown documentation
        @Nullable
        HelpText documentation();

        default String kind() {
            return getClass().getName();
        }

        /// a list of its arguments
        List<Argument> args();

        ///
        default String segment() {
            int idx = name().indexOf("/");
            if (idx == -1) {
                return "";
            }
            return name().substring(0, idx);
        }

        /// sender of this invocation
        default String sender() {
            return getClass().getSimpleName().startsWith("Server") ? "Client" : "Server";
        }

        ///
        default boolean isAsync() {
            return getClass().getSimpleName().endsWith("Notification");
        }
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
    public record ServerRequest(String name, @Nullable HelpText documentation, List<Argument> args,
            Type returnType)
            implements Endpoint {
    }

    ///
    public record ServerNotification(String name, @Nullable HelpText documentation,
            List<Argument> args)
            implements Endpoint {
    }

    ///
    public record ClientRequest(String name, @Nullable HelpText documentation, List<Argument> args,
            Type returnType)
            implements Endpoint {
    }

    ///
    public record ClientNotification(String name, @Nullable HelpText documentation,
            List<Argument> args)
            implements Endpoint {
    }

    ///
    public record Field(String name, /* Type */ String type, @Nullable HelpText documentation) {
        Field(String name, String type) {
            this(name, type, null);
        }
    }

    /// A data type
    public sealed interface Type {
        default String kind() {
            return getClass().getName();
        }

        /// Documentation of the data type
        @Nullable
        HelpText documentation();

        /// name of the data type
        String name();

        ///
        String identifier();
    }


    /// Typical built-in data types supported by the API
    public enum BuiltinType implements Type {
        INT, LONG, STRING, BOOL, DOUBLE;

        @Override
        public HelpText documentation() {
            return new HelpText("built-in data type", List.of());
        }

        public String identifier() {
            return name().toLowerCase();
        }

    }

    /// List of `type`.
    ///
    /// @param type the type of list elements
    public record ListType(Type type) implements Type {
        @Override
        public String name() {
            return type().name() + "[]";
        }

        public String identifier() {
            return type().identifier() + "[]";
        }

        @Override
        public @Nullable HelpText documentation() {
            return null;
        }
    }

    /// Data type of objects or struct or record.
    ///
    /// @param typeName short type name
    /// @param typeFullName fully-qualified type name
    /// @param fields list of fields
    /// @param documentation documentation of data type
    public record ObjectType(String typeName, String typeFullName, List<Field> fields,
            HelpText documentation) implements Type {
        @Override
        public String name() {
            return typeName;
        }

        public String identifier() {
            return typeFullName;
        }

        ///
        public @Nullable String jsonExample() {
            return DataExamples.get(typeFullName);
        }
    }

    /// A data type representing that a method returns or expecting either type `a` or `b`.
    ///
    /// @param a
    /// @param b
    public record EitherType(Type a, Type b) implements Type {

        @Override
        public String name() {
            return "either<a,b>";
        }

        public String identifier() {
            return name();
        }

        @Override
        public @Nullable HelpText documentation() {
            return null;
        }
    }

    /// Enumeration data type
    ///
    /// @param typeName short name of the data type
    /// @param typeFullName fully-qualified name
    /// @param values possible values of the enum
    /// @param documentation documentation of the data type
    public record EnumType(String typeName, String typeFullName, List<EnumConstant> values,
            HelpText documentation) implements Type {

        @Override
        public String name() {
            return typeName;
        }

        public String identifier() {
            return typeFullName;
        }

    }

    public record EnumConstant(String value, @Nullable HelpText documentation) {
    }

}
