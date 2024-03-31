/**
 *
 * @author Alexander Weigl 
 * @version 1 (31.03.24)
 */
module key.recoder {
    exports recoder;
    exports recoder.abstraction;
    exports recoder.convenience;
    exports recoder.java.declaration;
    exports recoder.java;
    exports recoder.java.reference;
    exports recoder.java.statement;
    exports recoder.list.generic;
    exports recoder.service;
    exports recoder.parser;
    exports recoder.io;
    exports recoder.java.expression;
    exports recoder.bytecode;
    exports recoder.java.expression.operator;
    exports recoder.util;
    exports recoder.java.declaration.modifier;
    exports recoder.kit;
    exports recoder.java.expression.literal;
    requires java.desktop;
    requires org.slf4j;
}