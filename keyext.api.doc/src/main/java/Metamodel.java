/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
import java.util.List;

import org.jspecify.annotations.NullMarked;

/**
 * @author Alexander Weigl
 * @version 1 (29.10.23)
 */
@NullMarked
public class Metamodel {
    public record KeyApi(
            List<Endpoint> endpoints,
            List<Type> types) {
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

    record ServerRequest(String name, String documentation, List<Argument> args, Type returnType) implements Endpoint {
    }

    record ServerNotification(String name, String documentation, List<Argument> args) implements Endpoint {
    }

    record ClientRequest(String name, String documentation, List<Argument> args, Type returnType) implements Endpoint {
    }

    record ClientNotification(String name, String documentation, List<Argument> args) implements Endpoint {
    }

    record Field(String name, /*Type*/ String type, String documentation) {

    Field(String name, String type) {
            this(name, type, "");
        }
}

public sealed


interface Type {
    default String kind() {
            return getClass().getSimpleName();
        }

    String documentation();

    String name();
}


enum BuiltinType implements Type {
    INT, LONG, STRING, BOOL, DOUBLE;

    @Override
    public String documentation() {
        return "built-in data type";
    }

    }

    record ListType(Type type, String documentation) implements Type {

    @Override
    public String name() {
        return type().name() + "[]";
    }

    }

    record ObjectType(String typeName, List<Field> fields, String documentation) implements Type {

    @Override
    public String name() {
        return typeName;
    }

    }

    public record EitherType(Type a, Type b, String documentation) implements Type {

    @Override
    public String name() {
        return "either<a,b>";
    }

    }

    public record EnumType(String typeName, List<String> values, String documentation) implements Type {

    @Override
    public String name() {
        return typeName;
    }
}}
