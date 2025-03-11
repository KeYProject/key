/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.parser;

public interface JavaCCParserConstants {

    int EOF = 0;
    int SINGLE_LINE_COMMENT = 9;
    int FORMAL_COMMENT = 10;
    int MULTI_LINE_COMMENT = 11;
    int ABSTRACT = 13;
    int ASSERT = 14;
    int AT = 15;
    int BOOLEAN = 16;
    int BREAK = 17;
    int BYTE = 18;
    int CASE = 19;
    int CATCH = 20;
    int CHAR = 21;
    int CLASS = 22;
    int CONST = 23;
    int CONTINUE = 24;
    int _DEFAULT = 25;
    int DO = 26;
    int DOUBLE = 27;
    int ELSE = 28;
    int ENUM = 29;
    int EXTENDS = 30;
    int FALSE = 31;
    int FINAL = 32;
    int FINALLY = 33;
    int FLOAT = 34;
    int FOR = 35;
    int GOTO = 36;
    int IF = 37;
    int IMPLEMENTS = 38;
    int IMPORT = 39;
    int INSTANCEOF = 40;
    int INT = 41;
    int INTERFACE = 42;
    int LONG = 43;
    int NATIVE = 44;
    int NEW = 45;
    int NULL = 46;
    int PACKAGE = 47;
    int PRIVATE = 48;
    int PROTECTED = 49;
    int PUBLIC = 50;
    int RETURN = 51;
    int SHORT = 52;
    int STATIC = 53;
    int SUPER = 54;
    int SWITCH = 55;
    int SYNCHRONIZED = 56;
    int THIS = 57;
    int THROW = 58;
    int THROWS = 59;
    int TRANSIENT = 60;
    int TRUE = 61;
    int TRY = 62;
    int VOID = 63;
    int VOLATILE = 64;
    int WHILE = 65;
    int VARARGDENOTER = 66;
    int STRICTFP = 67;
    int INTEGER_LITERAL = 68;
    int DECIMAL_LITERAL = 69;
    int HEX_LITERAL = 70;
    int OCTAL_LITERAL = 71;
    int FLOATING_POINT_LITERAL = 72;
    int EXPONENT = 73;
    int CHARACTER_LITERAL = 74;
    int STRING_LITERAL = 75;
    int IDENTIFIER = 76;
    int LETTER = 77;
    int PART_LETTER = 78;
    int LPAREN = 79;
    int RPAREN = 80;
    int LBRACE = 81;
    int RBRACE = 82;
    int LBRACKET = 83;
    int RBRACKET = 84;
    int SEMICOLON = 85;
    int COMMA = 86;
    int DOT = 87;
    int ASSIGN = 88;
    int LT = 89;
    int BANG = 90;
    int TILDE = 91;
    int HOOK = 92;
    int COLON = 93;
    int EQ = 94;
    int LE = 95;
    int GE = 96;
    int NE = 97;
    int SC_OR = 98;
    int SC_AND = 99;
    int INCR = 100;
    int DECR = 101;
    int PLUS = 102;
    int MINUS = 103;
    int STAR = 104;
    int SLASH = 105;
    int BIT_AND = 106;
    int BIT_OR = 107;
    int XOR = 108;
    int REM = 109;
    int LSHIFT = 110;
    int PLUSASSIGN = 111;
    int MINUSASSIGN = 112;
    int STARASSIGN = 113;
    int SLASHASSIGN = 114;
    int ANDASSIGN = 115;
    int ORASSIGN = 116;
    int XORASSIGN = 117;
    int REMASSIGN = 118;
    int LSHIFTASSIGN = 119;
    int RSIGNEDSHIFTASSIGN = 120;
    int RUNSIGNEDSHIFTASSIGN = 121;
    int RUNSIGNEDSHIFT = 122;
    int RSIGNEDSHIFT = 123;
    int GT = 124;

    int DEFAULT = 0;
    int IN_SINGLE_LINE_COMMENT = 1;
    int IN_FORMAL_COMMENT = 2;
    int IN_MULTI_LINE_COMMENT = 3;

    String[] tokenImage = { "<EOF>", "\" \"", "\"\\t\"", "\"\\n\"", "\"\\r\"", "\"\\f\"", "\"//\"",
        "<token of kind 7>", "\"/*\"", "<SINGLE_LINE_COMMENT>", "\"*/\"", "\"*/\"",
        "<token of kind 12>", "\"abstract\"", "\"assert\"", "\"@\"", "\"boolean\"", "\"break\"",
        "\"byte\"", "\"case\"", "\"catch\"", "\"char\"", "\"class\"", "\"const\"", "\"continue\"",
        "\"default\"", "\"do\"", "\"double\"", "\"else\"", "\"enum\"", "\"extends\"", "\"false\"",
        "\"final\"", "\"finally\"", "\"float\"", "\"for\"", "\"goto\"", "\"if\"", "\"implements\"",
        "\"import\"", "\"instanceof\"", "\"int\"", "\"interface\"", "\"long\"", "\"native\"",
        "\"new\"", "\"null\"", "\"package\"", "\"private\"", "\"protected\"", "\"public\"",
        "\"return\"", "\"short\"", "\"static\"", "\"super\"", "\"switch\"", "\"synchronized\"",
        "\"this\"", "\"throw\"", "\"throws\"", "\"transient\"", "\"true\"", "\"try\"", "\"void\"",
        "\"volatile\"", "\"while\"", "\"...\"", "\"strictfp\"", "<INTEGER_LITERAL>",
        "<DECIMAL_LITERAL>", "<HEX_LITERAL>", "<OCTAL_LITERAL>", "<FLOATING_POINT_LITERAL>",
        "<EXPONENT>", "<CHARACTER_LITERAL>", "<STRING_LITERAL>", "<IDENTIFIER>", "<LETTER>",
        "<PART_LETTER>", "\"(\"", "\")\"", "\"{\"", "\"}\"", "\"[\"", "\"]\"", "\";\"", "\",\"",
        "\".\"", "\"=\"", "\"<\"", "\"!\"", "\"~\"", "\"?\"", "\":\"", "\"==\"", "\"<=\"", "\">=\"",
        "\"!=\"", "\"||\"", "\"&&\"", "\"++\"", "\"--\"", "\"+\"", "\"-\"", "\"*\"", "\"/\"",
        "\"&\"", "\"|\"", "\"^\"", "\"%\"", "\"<<\"", "\"+=\"", "\"-=\"", "\"*=\"", "\"/=\"",
        "\"&=\"", "\"|=\"", "\"^=\"", "\"%=\"", "\"<<=\"", "\">>=\"", "\">>>=\"", "\">>>\"",
        "\">>\"", "\">\"", };

}
