/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.parser;

public class JavaCCParserTokenManager implements JavaCCParserConstants {
    public static final String[] jjstrLiteralImages = { "", null, null, null, null, null, null,
        null, null, null, null, null, null, "\141\142\163\164\162\141\143\164",
        "\141\163\163\145\162\164", "\100", "\142\157\157\154\145\141\156", "\142\162\145\141\153",
        "\142\171\164\145", "\143\141\163\145", "\143\141\164\143\150", "\143\150\141\162",
        "\143\154\141\163\163", "\143\157\156\163\164", "\143\157\156\164\151\156\165\145",
        "\144\145\146\141\165\154\164", "\144\157", "\144\157\165\142\154\145", "\145\154\163\145",
        "\145\156\165\155", "\145\170\164\145\156\144\163", "\146\141\154\163\145",
        "\146\151\156\141\154", "\146\151\156\141\154\154\171", "\146\154\157\141\164",
        "\146\157\162", "\147\157\164\157", "\151\146", "\151\155\160\154\145\155\145\156\164\163",
        "\151\155\160\157\162\164", "\151\156\163\164\141\156\143\145\157\146", "\151\156\164",
        "\151\156\164\145\162\146\141\143\145", "\154\157\156\147", "\156\141\164\151\166\145",
        "\156\145\167", "\156\165\154\154", "\160\141\143\153\141\147\145",
        "\160\162\151\166\141\164\145", "\160\162\157\164\145\143\164\145\144",
        "\160\165\142\154\151\143", "\162\145\164\165\162\156", "\163\150\157\162\164",
        "\163\164\141\164\151\143", "\163\165\160\145\162", "\163\167\151\164\143\150",
        "\163\171\156\143\150\162\157\156\151\172\145\144", "\164\150\151\163",
        "\164\150\162\157\167", "\164\150\162\157\167\163", "\164\162\141\156\163\151\145\156\164",
        "\164\162\165\145", "\164\162\171", "\166\157\151\144", "\166\157\154\141\164\151\154\145",
        "\167\150\151\154\145", "\56\56\56", "\163\164\162\151\143\164\146\160", null, null, null,
        null, null, null, null, null, null, null, null, "\50", "\51", "\173", "\175", "\133",
        "\135", "\73", "\54", "\56", "\75", "\74", "\41", "\176", "\77", "\72", "\75\75", "\74\75",
        "\76\75", "\41\75", "\174\174", "\46\46", "\53\53", "\55\55", "\53", "\55", "\52", "\57",
        "\46", "\174", "\136", "\45", "\74\74", "\53\75", "\55\75", "\52\75", "\57\75", "\46\75",
        "\174\75", "\136\75", "\45\75", "\74\74\75", "\76\76\75", "\76\76\76\75", "\76\76\76",
        "\76\76", "\76", };
    public static final String[] lexStateNames =
        { "DEFAULT", "IN_SINGLE_LINE_COMMENT", "IN_FORMAL_COMMENT", "IN_MULTI_LINE_COMMENT", };
    public static final int[] jjnewLexState = { -1, -1, -1, -1, -1, -1, 1, 2, 3, 0, 0, 0, -1, -1,
        -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1,
        -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1,
        -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1,
        -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1,
        -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, };
    static final long[] jjbitVec0 =
        { 0xfffffffffffffffeL, 0xffffffffffffffffL, 0xffffffffffffffffL, 0xffffffffffffffffL };
    static final long[] jjbitVec2 = { 0x0L, 0x0L, 0xffffffffffffffffL, 0xffffffffffffffffL };
    static final long[] jjbitVec3 =
        { 0xfff0000000200002L, 0xffffffffffffdfffL, 0xfffff00f7fffffffL, 0x12000000007fffffL };
    static final long[] jjbitVec4 = { 0x0L, 0x0L, 0x420043c00000000L, 0xff7fffffff7fffffL };
    static final long[] jjbitVec5 =
        { 0xffffcffffffffL, 0xffffffffffff0000L, 0xf9ff3fffffffffffL, 0x401f00030003L };
    static final long[] jjbitVec6 =
        { 0x0L, 0x400000000000000L, 0xfffffffbffffd740L, 0xffffffcff7fffL };
    static final long[] jjbitVec7 =
        { 0xffffffffffffffffL, 0xffffffffffffffffL, 0xfffffffffffff003L, 0x33fffffffff199fL };
    static final long[] jjbitVec8 =
        { 0xfffe000000000000L, 0xfffffffe027fffffL, 0xffL, 0x707ffffff0000L };
    static final long[] jjbitVec9 =
        { 0x7fffffe00000000L, 0xfffe0000000007ffL, 0xffffffffffffffffL, 0x1c000060002fffffL };
    static final long[] jjbitVec10 = { 0x1ffffffd0000L, 0x0L, 0x3fffffffffL, 0x0L };
    static final long[] jjbitVec11 =
        { 0x23ffffffffffffe0L, 0x3ff010000L, 0x3c5fdfffff99fe0L, 0xf0003b0000000L };
    static final long[] jjbitVec12 =
        { 0x36dfdfffff987e0L, 0x1c00005e000000L, 0x23edfdfffffbafe0L, 0x100010000L };
    static final long[] jjbitVec13 =
        { 0x23cdfdfffff99fe0L, 0x3b0000000L, 0x3bfc718d63dc7e0L, 0x0L };
    static final long[] jjbitVec14 =
        { 0x3effdfffffddfe0L, 0x300000000L, 0x3effdfffffddfe0L, 0x340000000L };
    static final long[] jjbitVec15 =
        { 0x3fffdfffffddfe0L, 0x300000000L, 0x2ffbfffffc7fffe0L, 0x7fL };
    static final long[] jjbitVec16 =
        { 0x800dfffffffffffeL, 0x7fL, 0x200decaefef02596L, 0x3000005fL };
    static final long[] jjbitVec17 = { 0x1L, 0x7fffffffeffL, 0xf00L, 0x0L };
    static final long[] jjbitVec18 =
        { 0x6fbffffffffL, 0x3f0000L, 0xffffffff00000000L, 0x7fffffffff003fL };
    static final long[] jjbitVec19 =
        { 0xffffffffffffffffL, 0xffffffff83ffffffL, 0xffffff07ffffffffL, 0x3ffffffffffffffL };
    static final long[] jjbitVec20 =
        { 0xffffffffffffff7fL, 0xffffffff3d7f3d7fL, 0x7f3d7fffffff3d7fL, 0xffff7fffff7f7f3dL };
    static final long[] jjbitVec21 =
        { 0xffffffff7f3d7fffL, 0x7ffff7fL, 0xffffffff00000000L, 0x1fffffffffffffL };
    static final long[] jjbitVec22 =
        { 0xffffffffffffffffL, 0x7f9fffffffffffL, 0xffffffff07fffffeL, 0x7ffffffffffL };
    static final long[] jjbitVec23 = { 0x0L, 0x0L, 0xfffffffffffffL, 0x8000000L };
    static final long[] jjbitVec24 =
        { 0xffffffff00000000L, 0xffffffffffffffL, 0x1ffffffffffL, 0x0L };
    static final long[] jjbitVec25 =
        { 0xffffffffffffffffL, 0xffffffffffffffffL, 0xffffffff0fffffffL, 0x3ffffffffffffffL };
    static final long[] jjbitVec26 =
        { 0xffffffff3f3fffffL, 0x3fffffffaaff3f3fL, 0x5fdfffffffffffffL, 0x1fdc1fff0fcf1fdcL };
    static final long[] jjbitVec27 =
        { 0x8000000000000000L, 0x8000000000000001L, 0xffff00000000L, 0x0L };
    static final long[] jjbitVec28 = { 0x3fbbd503e2ffc84L, 0xffffffff00000000L, 0xfL, 0x0L };
    static final long[] jjbitVec29 =
        { 0x73e03fe000000e0L, 0xfffffffffffffffeL, 0xfffffffe601fffffL, 0x7fffffffffffffffL };
    static final long[] jjbitVec30 =
        { 0xfffe1fffffffffe0L, 0xffffffffffffffffL, 0xffffff00007fffL, 0x0L };
    static final long[] jjbitVec31 =
        { 0xffffffffffffffffL, 0xffffffffffffffffL, 0x3fffffffffffffL, 0x0L };
    static final long[] jjbitVec32 =
        { 0xffffffffffffffffL, 0xffffffffffffffffL, 0x3fffffffffL, 0x0L };
    static final long[] jjbitVec33 = { 0xffffffffffffffffL, 0xffffffffffffffffL, 0x1fffL, 0x0L };
    static final long[] jjbitVec34 =
        { 0xffffffffffffffffL, 0xffffffffffffffffL, 0xfffffffffL, 0x0L };
    static final long[] jjbitVec35 = { 0x3fffffffffffL, 0x0L, 0x0L, 0x0L };
    static final long[] jjbitVec36 =
        { 0x5f7ffdffa0f8007fL, 0xffffffffffffffdbL, 0x3ffffffffffffL, 0xfffffffffff80000L };
    static final long[] jjbitVec37 =
        { 0x3fffffffffffffffL, 0xffffffffffff0000L, 0xfffffffffffcffffL, 0xfff0000000000ffL };
    static final long[] jjbitVec38 =
        { 0x18000000000000L, 0xffd702000000e000L, 0xffffffffffffffffL, 0x1fffffffffffffffL };
    static final long[] jjbitVec39 =
        { 0x87fffffe00000010L, 0xffffffe007fffffeL, 0x7fffffffffffffffL, 0x631cfcfcfcL };
    static final long[] jjbitVec40 = { 0x0L, 0x0L, 0x420043cffffffffL, 0xff7fffffff7fffffL };
    static final long[] jjbitVec41 =
        { 0xffffffffffffffffL, 0x400000700007fffL, 0xfffffffbffffd740L, 0xffffffcff7fffL };
    static final long[] jjbitVec42 =
        { 0xffffffffffffffffL, 0xffffffffffffffffL, 0xfffffffffffff07bL, 0x33fffffffff199fL };
    static final long[] jjbitVec43 =
        { 0xfffe000000000000L, 0xfffffffe027fffffL, 0xbbfffffbfffe00ffL, 0x707ffffff0016L };
    static final long[] jjbitVec44 =
        { 0x7fffffe00000000L, 0xffff03ff003fffffL, 0xffffffffffffffffL, 0x1fff3dff9fefffffL };
    static final long[] jjbitVec45 = { 0xffff1fffffff8000L, 0x7ffL, 0x1ffffffffffffL, 0x0L };
    static final long[] jjbitVec46 =
        { 0xf3ffffffffffffeeL, 0xffcfff1f3fffL, 0xd3c5fdfffff99feeL, 0xfffcfb080399fL };
    static final long[] jjbitVec47 =
        { 0xd36dfdfffff987e4L, 0x1fffc05e003987L, 0xf3edfdfffffbafeeL, 0xffc100013bbfL };
    static final long[] jjbitVec48 =
        { 0xf3cdfdfffff99feeL, 0xffc3b0c0398fL, 0xc3bfc718d63dc7ecL, 0xff8000803dc7L };
    static final long[] jjbitVec49 =
        { 0xc3effdfffffddfeeL, 0xffc300603ddfL, 0xc3effdfffffddfecL, 0xffc340603ddfL };
    static final long[] jjbitVec50 =
        { 0xc3fffdfffffddfecL, 0xffc300803dcfL, 0x2ffbfffffc7fffecL, 0xc0000ff5f847fL };
    static final long[] jjbitVec51 =
        { 0x87fffffffffffffeL, 0x3ff7fffL, 0x3bffecaefef02596L, 0x33ff3f5fL };
    static final long[] jjbitVec52 =
        { 0xc2a003ff03000001L, 0xfffe07fffffffeffL, 0x1ffffffffeff0fdfL, 0x40L };
    static final long[] jjbitVec53 =
        { 0x3c7f6fbffffffffL, 0x3ff03ffL, 0xffffffff00000000L, 0x7fffffffff003fL };
    static final long[] jjbitVec54 =
        { 0xffffffff7f3d7fffL, 0x3fe0007ffff7fL, 0xffffffff00000000L, 0x1fffffffffffffL };
    static final long[] jjbitVec55 = { 0x0L, 0x0L, 0xffffffffffffffffL, 0x3ff080fffffL };
    static final long[] jjbitVec56 =
        { 0xffffffff03ff7800L, 0xffffffffffffffL, 0x3ffffffffffL, 0x0L };
    static final long[] jjbitVec57 =
        { 0x80007c000000f000L, 0x8000fc0000000001L, 0xffff00000000L, 0x21fff0000L };
    static final long[] jjbitVec58 =
        { 0x73efffe000000e0L, 0xfffffffffffffffeL, 0xfffffffe661fffffL, 0x7fffffffffffffffL };
    static final long[] jjbitVec59 =
        { 0x5f7ffdffe0f8007fL, 0xffffffffffffffdbL, 0x3ffffffffffffL, 0xfffffffffff80000L };
    static final long[] jjbitVec60 =
        { 0x18000f00000000L, 0xffd702000000e000L, 0xffffffffffffffffL, 0x9fffffffffffffffL };
    static final long[] jjbitVec61 =
        { 0x87fffffe03ff0010L, 0xffffffe007fffffeL, 0x7fffffffffffffffL, 0xe0000631cfcfcfcL };
    static final int[] jjnextStates =
        { 34, 35, 40, 41, 44, 45, 12, 23, 24, 26, 14, 16, 49, 51, 6, 8, 9, 12, 23, 24, 28, 26, 36,
            37, 12, 44, 45, 12, 10, 11, 17, 18, 20, 25, 27, 29, 38, 39, 42, 43, 46, 47, };
    static final long[] jjtoToken = { 0xffffffffffffe001L, 0x1fffffffffff9d1fL, };
    static final long[] jjtoSkip = { 0xe3eL, 0x0L, };
    static final long[] jjtoSpecial = { 0xe00L, 0x0L, };
    static final long[] jjtoMore = { 0x11c0L, 0x0L, };
    static private final int[] jjrounds = new int[52];
    static private final int[] jjstateSet = new int[104];
    public static java.io.PrintStream debugStream = System.out;
    static protected JavaCharStream input_stream;
    static protected char curChar;
    static StringBuffer image;
    static int jjimageLen;
    static int lengthOfMatch;
    static int curLexState = 0;
    static final int defaultLexState = 0;
    static int jjnewStateCnt;
    static int jjround;
    static int jjmatchedPos;
    static int jjmatchedKind;

    public JavaCCParserTokenManager(JavaCharStream stream) {
        if (input_stream != null) {
            throw new TokenMgrError(
                "ERROR: Second call to constructor of static lexer. You must use ReInit() to initialize the static variables.",
                TokenMgrError.STATIC_LEXER_ERROR);
        }
        input_stream = stream;
    }

    public JavaCCParserTokenManager(JavaCharStream stream, int lexState) {
        this(stream);
        SwitchTo(lexState);
    }

    public static void setDebugStream(java.io.PrintStream ds) {
        debugStream = ds;
    }

    private static final int jjStopStringLiteralDfa_0(int pos, long active0, long active1) {
        switch (pos) {
        case 0:
            if ((active0 & 0x140L) != 0L || (active1 & 0x4020000000000L) != 0L) {
                return 2;
            }
            if ((active1 & 0x800004L) != 0L) {
                return 8;
            }
            if ((active0 & 0xffffffffffff6000L) != 0L || (active1 & 0xbL) != 0L) {
                jjmatchedKind = 76;
                return 32;
            }
            return -1;
        case 1:
            if ((active0 & 0xffffffdff3ff6000L) != 0L || (active1 & 0xbL) != 0L) {
                if (jjmatchedPos != 1) {
                    jjmatchedKind = 76;
                    jjmatchedPos = 1;
                }
                return 32;
            }
            if ((active0 & 0x100L) != 0L) {
                return 0;
            }
            if ((active0 & 0x200c000000L) != 0L) {
                return 32;
            }
            return -1;
        case 2:
            if ((active0 & 0xbfffd9d7fbff6000L) != 0L || (active1 & 0xbL) != 0L) {
                if (jjmatchedPos != 2) {
                    jjmatchedKind = 76;
                    jjmatchedPos = 2;
                }
                return 32;
            }
            if ((active0 & 0x4000260800000000L) != 0L) {
                return 32;
            }
            return -1;
        case 3:
            if ((active0 & 0x1dff95c7cbd36000L) != 0L || (active1 & 0xbL) != 0L) {
                jjmatchedKind = 76;
                jjmatchedPos = 3;
                return 32;
            }
            if ((active0 & 0xa2004810302c0000L) != 0L) {
                return 32;
            }
            return -1;
        case 4:
            if ((active0 & 0x11af95c04b016000L) != 0L || (active1 & 0x9L) != 0L) {
                if (jjmatchedPos != 4) {
                    jjmatchedKind = 76;
                    jjmatchedPos = 4;
                }
                return 32;
            }
            if ((active0 & 0xc50000780d20000L) != 0L || (active1 & 0x2L) != 0L) {
                return 32;
            }
            return -1;
        case 5:
            if ((active0 & 0x1103854243012000L) != 0L || (active1 & 0x9L) != 0L) {
                jjmatchedKind = 76;
                jjmatchedPos = 5;
                return 32;
            }
            if ((active0 & 0x8ac108008004000L) != 0L) {
                return 32;
            }
            return -1;
        case 6:
            if ((active0 & 0x1102054001002000L) != 0L || (active1 & 0x9L) != 0L) {
                jjmatchedKind = 76;
                jjmatchedPos = 6;
                return 32;
            }
            if ((active0 & 0x1800242010000L) != 0L) {
                return 32;
            }
            return -1;
        case 7:
            if ((active0 & 0x1102054000000000L) != 0L) {
                jjmatchedKind = 76;
                jjmatchedPos = 7;
                return 32;
            }
            if ((active0 & 0x1002000L) != 0L || (active1 & 0x9L) != 0L) {
                return 32;
            }
            return -1;
        case 8:
            if ((active0 & 0x100014000000000L) != 0L) {
                jjmatchedKind = 76;
                jjmatchedPos = 8;
                return 32;
            }
            if ((active0 & 0x1002040000000000L) != 0L) {
                return 32;
            }
            return -1;
        case 9:
            if ((active0 & 0x100000000000000L) != 0L) {
                jjmatchedKind = 76;
                jjmatchedPos = 9;
                return 32;
            }
            if ((active0 & 0x14000000000L) != 0L) {
                return 32;
            }
            return -1;
        case 10:
            if ((active0 & 0x100000000000000L) != 0L) {
                jjmatchedKind = 76;
                jjmatchedPos = 10;
                return 32;
            }
            return -1;
        default:
            return -1;
        }
    }

    private static final int jjStartNfa_0(int pos, long active0, long active1) {
        return jjMoveNfa_0(jjStopStringLiteralDfa_0(pos, active0, active1), pos + 1);
    }

    static private final int jjStopAtPos(int pos, int kind) {
        jjmatchedKind = kind;
        jjmatchedPos = pos;
        return pos + 1;
    }

    static private final int jjStartNfaWithStates_0(int pos, int kind, int state) {
        jjmatchedKind = kind;
        jjmatchedPos = pos;
        try {
            curChar = JavaCharStream.readChar();
        } catch (java.io.IOException e) {
            return pos + 1;
        }
        return jjMoveNfa_0(state, pos + 1);
    }

    static private final int jjMoveStringLiteralDfa0_0() {
        switch (curChar) {
        case 33:
            jjmatchedKind = 90;
            return jjMoveStringLiteralDfa1_0(0x0L, 0x200000000L);
        case 37:
            jjmatchedKind = 109;
            return jjMoveStringLiteralDfa1_0(0x0L, 0x40000000000000L);
        case 38:
            jjmatchedKind = 106;
            return jjMoveStringLiteralDfa1_0(0x0L, 0x8000800000000L);
        case 40:
            return jjStopAtPos(0, 79);
        case 41:
            return jjStopAtPos(0, 80);
        case 42:
            jjmatchedKind = 104;
            return jjMoveStringLiteralDfa1_0(0x0L, 0x2000000000000L);
        case 43:
            jjmatchedKind = 102;
            return jjMoveStringLiteralDfa1_0(0x0L, 0x801000000000L);
        case 44:
            return jjStopAtPos(0, 86);
        case 45:
            jjmatchedKind = 103;
            return jjMoveStringLiteralDfa1_0(0x0L, 0x1002000000000L);
        case 46:
            jjmatchedKind = 87;
            return jjMoveStringLiteralDfa1_0(0x0L, 0x4L);
        case 47:
            jjmatchedKind = 105;
            return jjMoveStringLiteralDfa1_0(0x140L, 0x4000000000000L);
        case 58:
            return jjStopAtPos(0, 93);
        case 59:
            return jjStopAtPos(0, 85);
        case 60:
            jjmatchedKind = 89;
            return jjMoveStringLiteralDfa1_0(0x0L, 0x80400080000000L);
        case 61:
            jjmatchedKind = 88;
            return jjMoveStringLiteralDfa1_0(0x0L, 0x40000000L);
        case 62:
            jjmatchedKind = 124;
            return jjMoveStringLiteralDfa1_0(0x0L, 0xf00000100000000L);
        case 63:
            return jjStopAtPos(0, 92);
        case 64:
            return jjStopAtPos(0, 15);
        case 91:
            return jjStopAtPos(0, 83);
        case 93:
            return jjStopAtPos(0, 84);
        case 94:
            jjmatchedKind = 108;
            return jjMoveStringLiteralDfa1_0(0x0L, 0x20000000000000L);
        case 97:
            return jjMoveStringLiteralDfa1_0(0x6000L, 0x0L);
        case 98:
            return jjMoveStringLiteralDfa1_0(0x70000L, 0x0L);
        case 99:
            return jjMoveStringLiteralDfa1_0(0x1f80000L, 0x0L);
        case 100:
            return jjMoveStringLiteralDfa1_0(0xe000000L, 0x0L);
        case 101:
            return jjMoveStringLiteralDfa1_0(0x70000000L, 0x0L);
        case 102:
            return jjMoveStringLiteralDfa1_0(0xf80000000L, 0x0L);
        case 103:
            return jjMoveStringLiteralDfa1_0(0x1000000000L, 0x0L);
        case 105:
            return jjMoveStringLiteralDfa1_0(0x7e000000000L, 0x0L);
        case 108:
            return jjMoveStringLiteralDfa1_0(0x80000000000L, 0x0L);
        case 110:
            return jjMoveStringLiteralDfa1_0(0x700000000000L, 0x0L);
        case 112:
            return jjMoveStringLiteralDfa1_0(0x7800000000000L, 0x0L);
        case 114:
            return jjMoveStringLiteralDfa1_0(0x8000000000000L, 0x0L);
        case 115:
            return jjMoveStringLiteralDfa1_0(0x1f0000000000000L, 0x8L);
        case 116:
            return jjMoveStringLiteralDfa1_0(0x7e00000000000000L, 0x0L);
        case 118:
            return jjMoveStringLiteralDfa1_0(0x8000000000000000L, 0x1L);
        case 119:
            return jjMoveStringLiteralDfa1_0(0x0L, 0x2L);
        case 123:
            return jjStopAtPos(0, 81);
        case 124:
            jjmatchedKind = 107;
            return jjMoveStringLiteralDfa1_0(0x0L, 0x10000400000000L);
        case 125:
            return jjStopAtPos(0, 82);
        case 126:
            return jjStopAtPos(0, 91);
        default:
            return jjMoveNfa_0(3, 0);
        }
    }

    static private final int jjMoveStringLiteralDfa1_0(long active0, long active1) {
        try {
            curChar = JavaCharStream.readChar();
        } catch (java.io.IOException e) {
            jjStopStringLiteralDfa_0(0, active0, active1);
            return 1;
        }
        switch (curChar) {
        case 38:
            if ((active1 & 0x800000000L) != 0L) {
                return jjStopAtPos(1, 99);
            }
            break;
        case 42:
            if ((active0 & 0x100L) != 0L) {
                return jjStartNfaWithStates_0(1, 8, 0);
            }
            break;
        case 43:
            if ((active1 & 0x1000000000L) != 0L) {
                return jjStopAtPos(1, 100);
            }
            break;
        case 45:
            if ((active1 & 0x2000000000L) != 0L) {
                return jjStopAtPos(1, 101);
            }
            break;
        case 46:
            return jjMoveStringLiteralDfa2_0(active0, 0L, active1, 0x4L);
        case 47:
            if ((active0 & 0x40L) != 0L) {
                return jjStopAtPos(1, 6);
            }
            break;
        case 60:
            if ((active1 & 0x400000000000L) != 0L) {
                jjmatchedKind = 110;
                jjmatchedPos = 1;
            }
            return jjMoveStringLiteralDfa2_0(active0, 0L, active1, 0x80000000000000L);
        case 61:
            if ((active1 & 0x40000000L) != 0L) {
                return jjStopAtPos(1, 94);
            } else if ((active1 & 0x80000000L) != 0L) {
                return jjStopAtPos(1, 95);
            } else if ((active1 & 0x100000000L) != 0L) {
                return jjStopAtPos(1, 96);
            } else if ((active1 & 0x200000000L) != 0L) {
                return jjStopAtPos(1, 97);
            } else if ((active1 & 0x800000000000L) != 0L) {
                return jjStopAtPos(1, 111);
            } else if ((active1 & 0x1000000000000L) != 0L) {
                return jjStopAtPos(1, 112);
            } else if ((active1 & 0x2000000000000L) != 0L) {
                return jjStopAtPos(1, 113);
            } else if ((active1 & 0x4000000000000L) != 0L) {
                return jjStopAtPos(1, 114);
            } else if ((active1 & 0x8000000000000L) != 0L) {
                return jjStopAtPos(1, 115);
            } else if ((active1 & 0x10000000000000L) != 0L) {
                return jjStopAtPos(1, 116);
            } else if ((active1 & 0x20000000000000L) != 0L) {
                return jjStopAtPos(1, 117);
            } else if ((active1 & 0x40000000000000L) != 0L) {
                return jjStopAtPos(1, 118);
            }
            break;
        case 62:
            if ((active1 & 0x800000000000000L) != 0L) {
                jjmatchedKind = 123;
                jjmatchedPos = 1;
            }
            return jjMoveStringLiteralDfa2_0(active0, 0L, active1, 0x700000000000000L);
        case 97:
            return jjMoveStringLiteralDfa2_0(active0, 0x900080180000L, active1, 0L);
        case 98:
            return jjMoveStringLiteralDfa2_0(active0, 0x2000L, active1, 0L);
        case 101:
            return jjMoveStringLiteralDfa2_0(active0, 0x8200002000000L, active1, 0L);
        case 102:
            if ((active0 & 0x2000000000L) != 0L) {
                return jjStartNfaWithStates_0(1, 37, 32);
            }
            break;
        case 104:
            return jjMoveStringLiteralDfa2_0(active0, 0xe10000000200000L, active1, 0x2L);
        case 105:
            return jjMoveStringLiteralDfa2_0(active0, 0x300000000L, active1, 0L);
        case 108:
            return jjMoveStringLiteralDfa2_0(active0, 0x410400000L, active1, 0L);
        case 109:
            return jjMoveStringLiteralDfa2_0(active0, 0xc000000000L, active1, 0L);
        case 110:
            return jjMoveStringLiteralDfa2_0(active0, 0x70020000000L, active1, 0L);
        case 111:
            if ((active0 & 0x4000000L) != 0L) {
                jjmatchedKind = 26;
                jjmatchedPos = 1;
            }
            return jjMoveStringLiteralDfa2_0(active0, 0x8000081809810000L, active1, 0x1L);
        case 114:
            return jjMoveStringLiteralDfa2_0(active0, 0x7003000000020000L, active1, 0L);
        case 115:
            return jjMoveStringLiteralDfa2_0(active0, 0x4000L, active1, 0L);
        case 116:
            return jjMoveStringLiteralDfa2_0(active0, 0x20000000000000L, active1, 0x8L);
        case 117:
            return jjMoveStringLiteralDfa2_0(active0, 0x44400000000000L, active1, 0L);
        case 119:
            return jjMoveStringLiteralDfa2_0(active0, 0x80000000000000L, active1, 0L);
        case 120:
            return jjMoveStringLiteralDfa2_0(active0, 0x40000000L, active1, 0L);
        case 121:
            return jjMoveStringLiteralDfa2_0(active0, 0x100000000040000L, active1, 0L);
        case 124:
            if ((active1 & 0x400000000L) != 0L) {
                return jjStopAtPos(1, 98);
            }
            break;
        default:
            break;
        }
        return jjStartNfa_0(0, active0, active1);
    }

    static private final int jjMoveStringLiteralDfa2_0(long old0, long active0, long old1,
            long active1) {
        if (((active0 &= old0) | (active1 &= old1)) == 0L) {
            return jjStartNfa_0(0, old0, old1);
        }
        try {
            curChar = JavaCharStream.readChar();
        } catch (java.io.IOException e) {
            jjStopStringLiteralDfa_0(1, active0, active1);
            return 2;
        }
        switch (curChar) {
        case 46:
            if ((active1 & 0x4L) != 0L) {
                return jjStopAtPos(2, 66);
            }
            break;
        case 61:
            if ((active1 & 0x80000000000000L) != 0L) {
                return jjStopAtPos(2, 119);
            } else if ((active1 & 0x100000000000000L) != 0L) {
                return jjStopAtPos(2, 120);
            }
            break;
        case 62:
            if ((active1 & 0x400000000000000L) != 0L) {
                jjmatchedKind = 122;
                jjmatchedPos = 2;
            }
            return jjMoveStringLiteralDfa3_0(active0, 0L, active1, 0x200000000000000L);
        case 97:
            return jjMoveStringLiteralDfa3_0(active0, 0x1020000000600000L, active1, 0L);
        case 98:
            return jjMoveStringLiteralDfa3_0(active0, 0x4000000000000L, active1, 0L);
        case 99:
            return jjMoveStringLiteralDfa3_0(active0, 0x800000000000L, active1, 0L);
        case 101:
            return jjMoveStringLiteralDfa3_0(active0, 0x20000L, active1, 0L);
        case 102:
            return jjMoveStringLiteralDfa3_0(active0, 0x2000000L, active1, 0L);
        case 105:
            return jjMoveStringLiteralDfa3_0(active0, 0x8281000000000000L, active1, 0x2L);
        case 108:
            return jjMoveStringLiteralDfa3_0(active0, 0x400080000000L, active1, 0x1L);
        case 110:
            return jjMoveStringLiteralDfa3_0(active0, 0x100080301800000L, active1, 0L);
        case 111:
            return jjMoveStringLiteralDfa3_0(active0, 0x12000400010000L, active1, 0L);
        case 112:
            return jjMoveStringLiteralDfa3_0(active0, 0x4000c000000000L, active1, 0L);
        case 114:
            if ((active0 & 0x800000000L) != 0L) {
                return jjStartNfaWithStates_0(2, 35, 32);
            }
            return jjMoveStringLiteralDfa3_0(active0, 0xc00000000000000L, active1, 0x8L);
        case 115:
            return jjMoveStringLiteralDfa3_0(active0, 0x10010086000L, active1, 0L);
        case 116:
            if ((active0 & 0x20000000000L) != 0L) {
                jjmatchedKind = 41;
                jjmatchedPos = 2;
            }
            return jjMoveStringLiteralDfa3_0(active0, 0x8141040140000L, active1, 0L);
        case 117:
            return jjMoveStringLiteralDfa3_0(active0, 0x2000000028000000L, active1, 0L);
        case 119:
            if ((active0 & 0x200000000000L) != 0L) {
                return jjStartNfaWithStates_0(2, 45, 32);
            }
            break;
        case 121:
            if ((active0 & 0x4000000000000000L) != 0L) {
                return jjStartNfaWithStates_0(2, 62, 32);
            }
            break;
        default:
            break;
        }
        return jjStartNfa_0(1, active0, active1);
    }

    static private final int jjMoveStringLiteralDfa3_0(long old0, long active0, long old1,
            long active1) {
        if (((active0 &= old0) | (active1 &= old1)) == 0L) {
            return jjStartNfa_0(1, old0, old1);
        }
        try {
            curChar = JavaCharStream.readChar();
        } catch (java.io.IOException e) {
            jjStopStringLiteralDfa_0(2, active0, active1);
            return 3;
        }
        switch (curChar) {
        case 61:
            if ((active1 & 0x200000000000000L) != 0L) {
                return jjStopAtPos(3, 121);
            }
            break;
        case 97:
            return jjMoveStringLiteralDfa4_0(active0, 0x702020000L, active1, 0x1L);
        case 98:
            return jjMoveStringLiteralDfa4_0(active0, 0x8000000L, active1, 0L);
        case 99:
            return jjMoveStringLiteralDfa4_0(active0, 0x100000000100000L, active1, 0L);
        case 100:
            if ((active0 & 0x8000000000000000L) != 0L) {
                return jjStartNfaWithStates_0(3, 63, 32);
            }
            break;
        case 101:
            if ((active0 & 0x40000L) != 0L) {
                return jjStartNfaWithStates_0(3, 18, 32);
            } else if ((active0 & 0x80000L) != 0L) {
                return jjStartNfaWithStates_0(3, 19, 32);
            } else if ((active0 & 0x10000000L) != 0L) {
                return jjStartNfaWithStates_0(3, 28, 32);
            } else if ((active0 & 0x2000000000000000L) != 0L) {
                return jjStartNfaWithStates_0(3, 61, 32);
            }
            return jjMoveStringLiteralDfa4_0(active0, 0x40040040004000L, active1, 0L);
        case 103:
            if ((active0 & 0x80000000000L) != 0L) {
                return jjStartNfaWithStates_0(3, 43, 32);
            }
            break;
        case 105:
            return jjMoveStringLiteralDfa4_0(active0, 0x100000000000L, active1, 0x8L);
        case 107:
            return jjMoveStringLiteralDfa4_0(active0, 0x800000000000L, active1, 0L);
        case 108:
            if ((active0 & 0x400000000000L) != 0L) {
                return jjStartNfaWithStates_0(3, 46, 32);
            }
            return jjMoveStringLiteralDfa4_0(active0, 0x4004000010000L, active1, 0x2L);
        case 109:
            if ((active0 & 0x20000000L) != 0L) {
                return jjStartNfaWithStates_0(3, 29, 32);
            }
            break;
        case 110:
            return jjMoveStringLiteralDfa4_0(active0, 0x1000000000000000L, active1, 0L);
        case 111:
            if ((active0 & 0x1000000000L) != 0L) {
                return jjStartNfaWithStates_0(3, 36, 32);
            }
            return jjMoveStringLiteralDfa4_0(active0, 0xc00008000000000L, active1, 0L);
        case 114:
            if ((active0 & 0x200000L) != 0L) {
                return jjStartNfaWithStates_0(3, 21, 32);
            }
            return jjMoveStringLiteralDfa4_0(active0, 0x10000000000000L, active1, 0L);
        case 115:
            if ((active0 & 0x200000000000000L) != 0L) {
                return jjStartNfaWithStates_0(3, 57, 32);
            }
            return jjMoveStringLiteralDfa4_0(active0, 0x80c00000L, active1, 0L);
        case 116:
            return jjMoveStringLiteralDfa4_0(active0, 0xa2010001002000L, active1, 0L);
        case 117:
            return jjMoveStringLiteralDfa4_0(active0, 0x8000000000000L, active1, 0L);
        case 118:
            return jjMoveStringLiteralDfa4_0(active0, 0x1000000000000L, active1, 0L);
        default:
            break;
        }
        return jjStartNfa_0(2, active0, active1);
    }

    static private final int jjMoveStringLiteralDfa4_0(long old0, long active0, long old1,
            long active1) {
        if (((active0 &= old0) | (active1 &= old1)) == 0L) {
            return jjStartNfa_0(2, old0, old1);
        }
        try {
            curChar = JavaCharStream.readChar();
        } catch (java.io.IOException e) {
            jjStopStringLiteralDfa_0(3, active0, active1);
            return 4;
        }
        switch (curChar) {
        case 97:
            return jjMoveStringLiteralDfa5_0(active0, 0x1810000000000L, active1, 0L);
        case 99:
            return jjMoveStringLiteralDfa5_0(active0, 0x80000000000000L, active1, 0x8L);
        case 101:
            if ((active0 & 0x80000000L) != 0L) {
                return jjStartNfaWithStates_0(4, 31, 32);
            } else if ((active1 & 0x2L) != 0L) {
                return jjStartNfaWithStates_0(4, 65, 32);
            }
            return jjMoveStringLiteralDfa5_0(active0, 0x2004000010000L, active1, 0L);
        case 104:
            if ((active0 & 0x100000L) != 0L) {
                return jjStartNfaWithStates_0(4, 20, 32);
            }
            return jjMoveStringLiteralDfa5_0(active0, 0x100000000000000L, active1, 0L);
        case 105:
            return jjMoveStringLiteralDfa5_0(active0, 0x24000001000000L, active1, 0L);
        case 107:
            if ((active0 & 0x20000L) != 0L) {
                return jjStartNfaWithStates_0(4, 17, 32);
            }
            break;
        case 108:
            if ((active0 & 0x100000000L) != 0L) {
                jjmatchedKind = 32;
                jjmatchedPos = 4;
            }
            return jjMoveStringLiteralDfa5_0(active0, 0x208000000L, active1, 0L);
        case 110:
            return jjMoveStringLiteralDfa5_0(active0, 0x40000000L, active1, 0L);
        case 114:
            if ((active0 & 0x40000000000000L) != 0L) {
                return jjStartNfaWithStates_0(4, 54, 32);
            }
            return jjMoveStringLiteralDfa5_0(active0, 0x8048000006000L, active1, 0L);
        case 115:
            if ((active0 & 0x400000L) != 0L) {
                return jjStartNfaWithStates_0(4, 22, 32);
            }
            return jjMoveStringLiteralDfa5_0(active0, 0x1000000000000000L, active1, 0L);
        case 116:
            if ((active0 & 0x800000L) != 0L) {
                return jjStartNfaWithStates_0(4, 23, 32);
            } else if ((active0 & 0x400000000L) != 0L) {
                return jjStartNfaWithStates_0(4, 34, 32);
            } else if ((active0 & 0x10000000000000L) != 0L) {
                return jjStartNfaWithStates_0(4, 52, 32);
            }
            return jjMoveStringLiteralDfa5_0(active0, 0L, active1, 0x1L);
        case 117:
            return jjMoveStringLiteralDfa5_0(active0, 0x2000000L, active1, 0L);
        case 118:
            return jjMoveStringLiteralDfa5_0(active0, 0x100000000000L, active1, 0L);
        case 119:
            if ((active0 & 0x400000000000000L) != 0L) {
                jjmatchedKind = 58;
                jjmatchedPos = 4;
            }
            return jjMoveStringLiteralDfa5_0(active0, 0x800000000000000L, active1, 0L);
        default:
            break;
        }
        return jjStartNfa_0(3, active0, active1);
    }

    static private final int jjMoveStringLiteralDfa5_0(long old0, long active0, long old1,
            long active1) {
        if (((active0 &= old0) | (active1 &= old1)) == 0L) {
            return jjStartNfa_0(3, old0, old1);
        }
        try {
            curChar = JavaCharStream.readChar();
        } catch (java.io.IOException e) {
            jjStopStringLiteralDfa_0(4, active0, active1);
            return 5;
        }
        switch (curChar) {
        case 97:
            return jjMoveStringLiteralDfa6_0(active0, 0x12000L, active1, 0L);
        case 99:
            if ((active0 & 0x4000000000000L) != 0L) {
                return jjStartNfaWithStates_0(5, 50, 32);
            } else if ((active0 & 0x20000000000000L) != 0L) {
                return jjStartNfaWithStates_0(5, 53, 32);
            }
            return jjMoveStringLiteralDfa6_0(active0, 0x2000000000000L, active1, 0L);
        case 100:
            return jjMoveStringLiteralDfa6_0(active0, 0x40000000L, active1, 0L);
        case 101:
            if ((active0 & 0x8000000L) != 0L) {
                return jjStartNfaWithStates_0(5, 27, 32);
            } else if ((active0 & 0x100000000000L) != 0L) {
                return jjStartNfaWithStates_0(5, 44, 32);
            }
            break;
        case 102:
            return jjMoveStringLiteralDfa6_0(active0, 0x40000000000L, active1, 0L);
        case 103:
            return jjMoveStringLiteralDfa6_0(active0, 0x800000000000L, active1, 0L);
        case 104:
            if ((active0 & 0x80000000000000L) != 0L) {
                return jjStartNfaWithStates_0(5, 55, 32);
            }
            break;
        case 105:
            return jjMoveStringLiteralDfa6_0(active0, 0x1000000000000000L, active1, 0x1L);
        case 108:
            return jjMoveStringLiteralDfa6_0(active0, 0x202000000L, active1, 0L);
        case 109:
            return jjMoveStringLiteralDfa6_0(active0, 0x4000000000L, active1, 0L);
        case 110:
            if ((active0 & 0x8000000000000L) != 0L) {
                return jjStartNfaWithStates_0(5, 51, 32);
            }
            return jjMoveStringLiteralDfa6_0(active0, 0x10001000000L, active1, 0L);
        case 114:
            return jjMoveStringLiteralDfa6_0(active0, 0x100000000000000L, active1, 0L);
        case 115:
            if ((active0 & 0x800000000000000L) != 0L) {
                return jjStartNfaWithStates_0(5, 59, 32);
            }
            break;
        case 116:
            if ((active0 & 0x4000L) != 0L) {
                return jjStartNfaWithStates_0(5, 14, 32);
            } else if ((active0 & 0x8000000000L) != 0L) {
                return jjStartNfaWithStates_0(5, 39, 32);
            }
            return jjMoveStringLiteralDfa6_0(active0, 0x1000000000000L, active1, 0x8L);
        default:
            break;
        }
        return jjStartNfa_0(4, active0, active1);
    }

    static private final int jjMoveStringLiteralDfa6_0(long old0, long active0, long old1,
            long active1) {
        if (((active0 &= old0) | (active1 &= old1)) == 0L) {
            return jjStartNfa_0(4, old0, old1);
        }
        try {
            curChar = JavaCharStream.readChar();
        } catch (java.io.IOException e) {
            jjStopStringLiteralDfa_0(5, active0, active1);
            return 6;
        }
        switch (curChar) {
        case 97:
            return jjMoveStringLiteralDfa7_0(active0, 0x40000000000L, active1, 0L);
        case 99:
            return jjMoveStringLiteralDfa7_0(active0, 0x10000002000L, active1, 0L);
        case 101:
            if ((active0 & 0x800000000000L) != 0L) {
                return jjStartNfaWithStates_0(6, 47, 32);
            } else if ((active0 & 0x1000000000000L) != 0L) {
                return jjStartNfaWithStates_0(6, 48, 32);
            }
            return jjMoveStringLiteralDfa7_0(active0, 0x1000004000000000L, active1, 0L);
        case 102:
            return jjMoveStringLiteralDfa7_0(active0, 0L, active1, 0x8L);
        case 108:
            return jjMoveStringLiteralDfa7_0(active0, 0L, active1, 0x1L);
        case 110:
            if ((active0 & 0x10000L) != 0L) {
                return jjStartNfaWithStates_0(6, 16, 32);
            }
            break;
        case 111:
            return jjMoveStringLiteralDfa7_0(active0, 0x100000000000000L, active1, 0L);
        case 115:
            if ((active0 & 0x40000000L) != 0L) {
                return jjStartNfaWithStates_0(6, 30, 32);
            }
            break;
        case 116:
            if ((active0 & 0x2000000L) != 0L) {
                return jjStartNfaWithStates_0(6, 25, 32);
            }
            return jjMoveStringLiteralDfa7_0(active0, 0x2000000000000L, active1, 0L);
        case 117:
            return jjMoveStringLiteralDfa7_0(active0, 0x1000000L, active1, 0L);
        case 121:
            if ((active0 & 0x200000000L) != 0L) {
                return jjStartNfaWithStates_0(6, 33, 32);
            }
            break;
        default:
            break;
        }
        return jjStartNfa_0(5, active0, active1);
    }

    static private final int jjMoveStringLiteralDfa7_0(long old0, long active0, long old1,
            long active1) {
        if (((active0 &= old0) | (active1 &= old1)) == 0L) {
            return jjStartNfa_0(5, old0, old1);
        }
        try {
            curChar = JavaCharStream.readChar();
        } catch (java.io.IOException e) {
            jjStopStringLiteralDfa_0(6, active0, active1);
            return 7;
        }
        switch (curChar) {
        case 99:
            return jjMoveStringLiteralDfa8_0(active0, 0x40000000000L, active1, 0L);
        case 101:
            if ((active0 & 0x1000000L) != 0L) {
                return jjStartNfaWithStates_0(7, 24, 32);
            } else if ((active1 & 0x1L) != 0L) {
                return jjStartNfaWithStates_0(7, 64, 32);
            }
            return jjMoveStringLiteralDfa8_0(active0, 0x2010000000000L, active1, 0L);
        case 110:
            return jjMoveStringLiteralDfa8_0(active0, 0x1100004000000000L, active1, 0L);
        case 112:
            if ((active1 & 0x8L) != 0L) {
                return jjStartNfaWithStates_0(7, 67, 32);
            }
            break;
        case 116:
            if ((active0 & 0x2000L) != 0L) {
                return jjStartNfaWithStates_0(7, 13, 32);
            }
            break;
        default:
            break;
        }
        return jjStartNfa_0(6, active0, active1);
    }

    static private final int jjMoveStringLiteralDfa8_0(long old0, long active0, long old1,
            long active1) {
        if (((active0 &= old0) | (active1 &= old1)) == 0L) {
            return jjStartNfa_0(6, old0, old1);
        }
        try {
            curChar = JavaCharStream.readChar();
        } catch (java.io.IOException e) {
            jjStopStringLiteralDfa_0(7, active0, 0L);
            return 8;
        }
        switch (curChar) {
        case 100:
            if ((active0 & 0x2000000000000L) != 0L) {
                return jjStartNfaWithStates_0(8, 49, 32);
            }
            break;
        case 101:
            if ((active0 & 0x40000000000L) != 0L) {
                return jjStartNfaWithStates_0(8, 42, 32);
            }
            break;
        case 105:
            return jjMoveStringLiteralDfa9_0(active0, 0x100000000000000L);
        case 111:
            return jjMoveStringLiteralDfa9_0(active0, 0x10000000000L);
        case 116:
            if ((active0 & 0x1000000000000000L) != 0L) {
                return jjStartNfaWithStates_0(8, 60, 32);
            }
            return jjMoveStringLiteralDfa9_0(active0, 0x4000000000L);
        default:
            break;
        }
        return jjStartNfa_0(7, active0, 0L);
    }

    static private final int jjMoveStringLiteralDfa9_0(long old0, long active0) {
        if (((active0 &= old0)) == 0L) {
            return jjStartNfa_0(7, old0, 0L);
        }
        try {
            curChar = JavaCharStream.readChar();
        } catch (java.io.IOException e) {
            jjStopStringLiteralDfa_0(8, active0, 0L);
            return 9;
        }
        switch (curChar) {
        case 102:
            if ((active0 & 0x10000000000L) != 0L) {
                return jjStartNfaWithStates_0(9, 40, 32);
            }
            break;
        case 115:
            if ((active0 & 0x4000000000L) != 0L) {
                return jjStartNfaWithStates_0(9, 38, 32);
            }
            break;
        case 122:
            return jjMoveStringLiteralDfa10_0(active0, 0x100000000000000L);
        default:
            break;
        }
        return jjStartNfa_0(8, active0, 0L);
    }

    static private final int jjMoveStringLiteralDfa10_0(long old0, long active0) {
        if (((active0 &= old0)) == 0L) {
            return jjStartNfa_0(8, old0, 0L);
        }
        try {
            curChar = JavaCharStream.readChar();
        } catch (java.io.IOException e) {
            jjStopStringLiteralDfa_0(9, active0, 0L);
            return 10;
        }
        switch (curChar) {
        case 101:
            return jjMoveStringLiteralDfa11_0(active0, 0x100000000000000L);
        default:
            break;
        }
        return jjStartNfa_0(9, active0, 0L);
    }

    static private final int jjMoveStringLiteralDfa11_0(long old0, long active0) {
        if (((active0 &= old0)) == 0L) {
            return jjStartNfa_0(9, old0, 0L);
        }
        try {
            curChar = JavaCharStream.readChar();
        } catch (java.io.IOException e) {
            jjStopStringLiteralDfa_0(10, active0, 0L);
            return 11;
        }
        switch (curChar) {
        case 100:
            if ((active0 & 0x100000000000000L) != 0L) {
                return jjStartNfaWithStates_0(11, 56, 32);
            }
            break;
        default:
            break;
        }
        return jjStartNfa_0(10, active0, 0L);
    }

    static private final void jjCheckNAdd(int state) {
        if (jjrounds[state] != jjround) {
            jjstateSet[jjnewStateCnt++] = state;
            jjrounds[state] = jjround;
        }
    }

    static private final void jjAddStates(int start, int end) {
        do {
            jjstateSet[jjnewStateCnt++] = jjnextStates[start];
        } while (start++ != end);
    }

    static private final void jjCheckNAddTwoStates(int state1, int state2) {
        jjCheckNAdd(state1);
        jjCheckNAdd(state2);
    }

    static private final void jjCheckNAddStates(int start, int end) {
        do {
            jjCheckNAdd(jjnextStates[start]);
        } while (start++ != end);
    }

    static private final void jjCheckNAddStates(int start) {
        jjCheckNAdd(jjnextStates[start]);
        jjCheckNAdd(jjnextStates[start + 1]);
    }

    static private final int jjMoveNfa_0(int startState, int curPos) {
        int[] nextStates;
        int startsAt = 0;
        jjnewStateCnt = 52;
        int i = 1;
        jjstateSet[0] = startState;
        int j, kind = 0x7fffffff;
        for (;;) {
            if (++jjround == 0x7fffffff) {
                ReInitRounds();
            }
            if (curChar < 64) {
                long l = 1L << curChar;
                do {
                    switch (jjstateSet[--i]) {
                    case 3:
                        if ((0x3ff000000000000L & l) != 0L) {
                            jjCheckNAddStates(0, 6);
                        } else if (curChar == 36) {
                            if (kind > 76) {
                                kind = 76;
                            }
                            jjCheckNAdd(32);
                        } else if (curChar == 34) {
                            jjCheckNAddStates(7, 9);
                        } else if (curChar == 39) {
                            jjAddStates(10, 11);
                        } else if (curChar == 46) {
                            jjCheckNAdd(8);
                        } else if (curChar == 47) {
                            jjstateSet[jjnewStateCnt++] = 2;
                        }
                        if ((0x3fe000000000000L & l) != 0L) {
                            if (kind > 68) {
                                kind = 68;
                            }
                            jjCheckNAddTwoStates(5, 6);
                        } else if (curChar == 48) {
                            if (kind > 68) {
                                kind = 68;
                            }
                            jjCheckNAddStates(12, 14);
                        }
                        break;
                    case 0:
                        if (curChar == 42) {
                            jjstateSet[jjnewStateCnt++] = 1;
                        }
                        break;
                    case 1:
                        if ((0xffff7fffffffffffL & l) != 0L && kind > 7) {
                            kind = 7;
                        }
                        break;
                    case 2:
                        if (curChar == 42) {
                            jjstateSet[jjnewStateCnt++] = 0;
                        }
                        break;
                    case 4:
                        if ((0x3fe000000000000L & l) == 0L) {
                            break;
                        }
                        if (kind > 68) {
                            kind = 68;
                        }
                        jjCheckNAddTwoStates(5, 6);
                        break;
                    case 5:
                        if ((0x3ff000000000000L & l) == 0L) {
                            break;
                        }
                        if (kind > 68) {
                            kind = 68;
                        }
                        jjCheckNAddTwoStates(5, 6);
                        break;
                    case 7:
                        if (curChar == 46) {
                            jjCheckNAdd(8);
                        }
                        break;
                    case 8:
                        if ((0x3ff000000000000L & l) == 0L) {
                            break;
                        }
                        if (kind > 72) {
                            kind = 72;
                        }
                        jjCheckNAddStates(15, 17);
                        break;
                    case 10:
                        if ((0x280000000000L & l) != 0L) {
                            jjCheckNAdd(11);
                        }
                        break;
                    case 11:
                        if ((0x3ff000000000000L & l) == 0L) {
                            break;
                        }
                        if (kind > 72) {
                            kind = 72;
                        }
                        jjCheckNAddTwoStates(11, 12);
                        break;
                    case 13:
                        if (curChar == 39) {
                            jjAddStates(10, 11);
                        }
                        break;
                    case 14:
                        if ((0xffffff7fffffdbffL & l) != 0L) {
                            jjCheckNAdd(15);
                        }
                        break;
                    case 15:
                        if (curChar == 39 && kind > 74) {
                            kind = 74;
                        }
                        break;
                    case 17:
                        if ((0x8400000000L & l) != 0L) {
                            jjCheckNAdd(15);
                        }
                        break;
                    case 18:
                        if ((0xff000000000000L & l) != 0L) {
                            jjCheckNAddTwoStates(19, 15);
                        }
                        break;
                    case 19:
                        if ((0xff000000000000L & l) != 0L) {
                            jjCheckNAdd(15);
                        }
                        break;
                    case 20:
                        if ((0xf000000000000L & l) != 0L) {
                            jjstateSet[jjnewStateCnt++] = 21;
                        }
                        break;
                    case 21:
                        if ((0xff000000000000L & l) != 0L) {
                            jjCheckNAdd(19);
                        }
                        break;
                    case 22:
                        if (curChar == 34) {
                            jjCheckNAddStates(7, 9);
                        }
                        break;
                    case 23:
                        if ((0xfffffffbffffdbffL & l) != 0L) {
                            jjCheckNAddStates(7, 9);
                        }
                        break;
                    case 25:
                        if ((0x8400000000L & l) != 0L) {
                            jjCheckNAddStates(7, 9);
                        }
                        break;
                    case 26:
                        if (curChar == 34 && kind > 75) {
                            kind = 75;
                        }
                        break;
                    case 27:
                        if ((0xff000000000000L & l) != 0L) {
                            jjCheckNAddStates(18, 21);
                        }
                        break;
                    case 28:
                        if ((0xff000000000000L & l) != 0L) {
                            jjCheckNAddStates(7, 9);
                        }
                        break;
                    case 29:
                        if ((0xf000000000000L & l) != 0L) {
                            jjstateSet[jjnewStateCnt++] = 30;
                        }
                        break;
                    case 30:
                        if ((0xff000000000000L & l) != 0L) {
                            jjCheckNAdd(28);
                        }
                        break;
                    case 31:
                        if (curChar != 36) {
                            break;
                        }
                        if (kind > 76) {
                            kind = 76;
                        }
                        jjCheckNAdd(32);
                        break;
                    case 32:
                        if ((0x3ff00100fffc1ffL & l) == 0L) {
                            break;
                        }
                        if (kind > 76) {
                            kind = 76;
                        }
                        jjCheckNAdd(32);
                        break;
                    case 33:
                        if ((0x3ff000000000000L & l) != 0L) {
                            jjCheckNAddStates(0, 6);
                        }
                        break;
                    case 34:
                        if ((0x3ff000000000000L & l) != 0L) {
                            jjCheckNAddTwoStates(34, 35);
                        }
                        break;
                    case 35:
                        if (curChar != 46) {
                            break;
                        }
                        if (kind > 72) {
                            kind = 72;
                        }
                        jjCheckNAddStates(22, 24);
                        break;
                    case 36:
                        if ((0x3ff000000000000L & l) == 0L) {
                            break;
                        }
                        if (kind > 72) {
                            kind = 72;
                        }
                        jjCheckNAddStates(22, 24);
                        break;
                    case 38:
                        if ((0x280000000000L & l) != 0L) {
                            jjCheckNAdd(39);
                        }
                        break;
                    case 39:
                        if ((0x3ff000000000000L & l) == 0L) {
                            break;
                        }
                        if (kind > 72) {
                            kind = 72;
                        }
                        jjCheckNAddTwoStates(39, 12);
                        break;
                    case 40:
                        if ((0x3ff000000000000L & l) != 0L) {
                            jjCheckNAddTwoStates(40, 41);
                        }
                        break;
                    case 42:
                        if ((0x280000000000L & l) != 0L) {
                            jjCheckNAdd(43);
                        }
                        break;
                    case 43:
                        if ((0x3ff000000000000L & l) == 0L) {
                            break;
                        }
                        if (kind > 72) {
                            kind = 72;
                        }
                        jjCheckNAddTwoStates(43, 12);
                        break;
                    case 44:
                        if ((0x3ff000000000000L & l) != 0L) {
                            jjCheckNAddStates(25, 27);
                        }
                        break;
                    case 46:
                        if ((0x280000000000L & l) != 0L) {
                            jjCheckNAdd(47);
                        }
                        break;
                    case 47:
                        if ((0x3ff000000000000L & l) != 0L) {
                            jjCheckNAddTwoStates(47, 12);
                        }
                        break;
                    case 48:
                        if (curChar != 48) {
                            break;
                        }
                        if (kind > 68) {
                            kind = 68;
                        }
                        jjCheckNAddStates(12, 14);
                        break;
                    case 50:
                        if ((0x3ff000000000000L & l) == 0L) {
                            break;
                        }
                        if (kind > 68) {
                            kind = 68;
                        }
                        jjCheckNAddTwoStates(50, 6);
                        break;
                    case 51:
                        if ((0xff000000000000L & l) == 0L) {
                            break;
                        }
                        if (kind > 68) {
                            kind = 68;
                        }
                        jjCheckNAddTwoStates(51, 6);
                        break;
                    default:
                        break;
                    }
                } while (i != startsAt);
            } else if (curChar < 128) {
                long l = 1L << (curChar & 077);
                do {
                    switch (jjstateSet[--i]) {
                    case 3:
                        if ((0x7fffffe87fffffeL & l) == 0L) {
                            break;
                        }
                        if (kind > 76) {
                            kind = 76;
                        }
                        jjCheckNAdd(32);
                        break;
                    case 1:
                        if (kind > 7) {
                            kind = 7;
                        }
                        break;
                    case 6:
                        if ((0x100000001000L & l) != 0L && kind > 68) {
                            kind = 68;
                        }
                        break;
                    case 9:
                        if ((0x2000000020L & l) != 0L) {
                            jjAddStates(28, 29);
                        }
                        break;
                    case 12:
                        if ((0x5000000050L & l) != 0L && kind > 72) {
                            kind = 72;
                        }
                        break;
                    case 14:
                        if ((0xffffffffefffffffL & l) != 0L) {
                            jjCheckNAdd(15);
                        }
                        break;
                    case 16:
                        if (curChar == 92) {
                            jjAddStates(30, 32);
                        }
                        break;
                    case 17:
                        if ((0x14404410000000L & l) != 0L) {
                            jjCheckNAdd(15);
                        }
                        break;
                    case 23:
                        if ((0xffffffffefffffffL & l) != 0L) {
                            jjCheckNAddStates(7, 9);
                        }
                        break;
                    case 24:
                        if (curChar == 92) {
                            jjAddStates(33, 35);
                        }
                        break;
                    case 25:
                        if ((0x14404410000000L & l) != 0L) {
                            jjCheckNAddStates(7, 9);
                        }
                        break;
                    case 32:
                        if ((0x87fffffe87fffffeL & l) == 0L) {
                            break;
                        }
                        if (kind > 76) {
                            kind = 76;
                        }
                        jjCheckNAdd(32);
                        break;
                    case 37:
                        if ((0x2000000020L & l) != 0L) {
                            jjAddStates(36, 37);
                        }
                        break;
                    case 41:
                        if ((0x2000000020L & l) != 0L) {
                            jjAddStates(38, 39);
                        }
                        break;
                    case 45:
                        if ((0x2000000020L & l) != 0L) {
                            jjAddStates(40, 41);
                        }
                        break;
                    case 49:
                        if ((0x100000001000000L & l) != 0L) {
                            jjCheckNAdd(50);
                        }
                        break;
                    case 50:
                        if ((0x7e0000007eL & l) == 0L) {
                            break;
                        }
                        if (kind > 68) {
                            kind = 68;
                        }
                        jjCheckNAddTwoStates(50, 6);
                        break;
                    default:
                        break;
                    }
                } while (i != startsAt);
            } else {
                int hiByte = curChar >> 8;
                int i1 = hiByte >> 6;
                long l1 = 1L << (hiByte & 077);
                int i2 = (curChar & 0xff) >> 6;
                long l2 = 1L << (curChar & 077);
                do {
                    switch (jjstateSet[--i]) {
                    case 3:
                        if (!jjCanMove_1(hiByte, i1, i2, l1, l2)) {
                            break;
                        }
                        if (kind > 76) {
                            kind = 76;
                        }
                        jjCheckNAdd(32);
                        break;
                    case 1:
                        if (jjCanMove_0(hiByte, i1, i2, l1, l2) && kind > 7) {
                            kind = 7;
                        }
                        break;
                    case 14:
                        if (jjCanMove_0(hiByte, i1, i2, l1, l2)) {
                            jjstateSet[jjnewStateCnt++] = 15;
                        }
                        break;
                    case 23:
                        if (jjCanMove_0(hiByte, i1, i2, l1, l2)) {
                            jjAddStates(7, 9);
                        }
                        break;
                    case 32:
                        if (!jjCanMove_2(hiByte, i1, i2, l1, l2)) {
                            break;
                        }
                        if (kind > 76) {
                            kind = 76;
                        }
                        jjCheckNAdd(32);
                        break;
                    default:
                        break;
                    }
                } while (i != startsAt);
            }
            if (kind != 0x7fffffff) {
                jjmatchedKind = kind;
                jjmatchedPos = curPos;
                kind = 0x7fffffff;
            }
            ++curPos;
            if ((i = jjnewStateCnt) == (startsAt = 52 - (jjnewStateCnt = startsAt))) {
                return curPos;
            }
            try {
                curChar = JavaCharStream.readChar();
            } catch (java.io.IOException e) {
                return curPos;
            }
        }
    }

    static private final int jjMoveStringLiteralDfa0_3() {
        switch (curChar) {
        case 42:
            return jjMoveStringLiteralDfa1_3(0x800L);
        default:
            return 1;
        }
    }

    static private final int jjMoveStringLiteralDfa1_3(long active0) {
        try {
            curChar = JavaCharStream.readChar();
        } catch (java.io.IOException e) {
            return 1;
        }
        switch (curChar) {
        case 47:
            if ((active0 & 0x800L) != 0L) {
                return jjStopAtPos(1, 11);
            }
            break;
        default:
            return 2;
        }
        return 2;
    }

    static private final int jjMoveStringLiteralDfa0_1() {
        return jjMoveNfa_1(0, 0);
    }

    static private final int jjMoveNfa_1(int startState, int curPos) {
        int[] nextStates;
        int startsAt = 0;
        jjnewStateCnt = 3;
        int i = 1;
        jjstateSet[0] = startState;
        int j, kind = 0x7fffffff;
        for (;;) {
            if (++jjround == 0x7fffffff) {
                ReInitRounds();
            }
            if (curChar < 64) {
                long l = 1L << curChar;
                do {
                    switch (jjstateSet[--i]) {
                    case 0:
                        if ((0x2400L & l) != 0L) {
                            if (kind > 9) {
                                kind = 9;
                            }
                        }
                        if (curChar == 13) {
                            jjstateSet[jjnewStateCnt++] = 1;
                        }
                        break;
                    case 1:
                        if (curChar == 10 && kind > 9) {
                            kind = 9;
                        }
                        break;
                    case 2:
                        if (curChar == 13) {
                            jjstateSet[jjnewStateCnt++] = 1;
                        }
                        break;
                    default:
                        break;
                    }
                } while (i != startsAt);
            } else if (curChar < 128) {
                long l = 1L << (curChar & 077);
                do {
                    switch (jjstateSet[--i]) {
                    default:
                        break;
                    }
                } while (i != startsAt);
            } else {
                int hiByte = curChar >> 8;
                int i1 = hiByte >> 6;
                long l1 = 1L << (hiByte & 077);
                int i2 = (curChar & 0xff) >> 6;
                long l2 = 1L << (curChar & 077);
                do {
                    switch (jjstateSet[--i]) {
                    default:
                        break;
                    }
                } while (i != startsAt);
            }
            if (kind != 0x7fffffff) {
                jjmatchedKind = kind;
                jjmatchedPos = curPos;
                kind = 0x7fffffff;
            }
            ++curPos;
            if ((i = jjnewStateCnt) == (startsAt = 3 - (jjnewStateCnt = startsAt))) {
                return curPos;
            }
            try {
                curChar = JavaCharStream.readChar();
            } catch (java.io.IOException e) {
                return curPos;
            }
        }
    }

    static private final int jjMoveStringLiteralDfa0_2() {
        switch (curChar) {
        case 42:
            return jjMoveStringLiteralDfa1_2(0x400L);
        default:
            return 1;
        }
    }

    static private final int jjMoveStringLiteralDfa1_2(long active0) {
        try {
            curChar = JavaCharStream.readChar();
        } catch (java.io.IOException e) {
            return 1;
        }
        switch (curChar) {
        case 47:
            if ((active0 & 0x400L) != 0L) {
                return jjStopAtPos(1, 10);
            }
            break;
        default:
            return 2;
        }
        return 2;
    }

    private static final boolean jjCanMove_0(int hiByte, int i1, int i2, long l1, long l2) {
        switch (hiByte) {
        case 0:
            return ((jjbitVec2[i2] & l2) != 0L);
        default:
            return (jjbitVec0[i1] & l1) != 0L;
        }
    }

    private static final boolean jjCanMove_1(int hiByte, int i1, int i2, long l1, long l2) {
        switch (hiByte) {
        case 0:
            return ((jjbitVec4[i2] & l2) != 0L);
        case 2:
            return ((jjbitVec5[i2] & l2) != 0L);
        case 3:
            return ((jjbitVec6[i2] & l2) != 0L);
        case 4:
            return ((jjbitVec7[i2] & l2) != 0L);
        case 5:
            return ((jjbitVec8[i2] & l2) != 0L);
        case 6:
            return ((jjbitVec9[i2] & l2) != 0L);
        case 7:
            return ((jjbitVec10[i2] & l2) != 0L);
        case 9:
            return ((jjbitVec11[i2] & l2) != 0L);
        case 10:
            return ((jjbitVec12[i2] & l2) != 0L);
        case 11:
            return ((jjbitVec13[i2] & l2) != 0L);
        case 12:
            return ((jjbitVec14[i2] & l2) != 0L);
        case 13:
            return ((jjbitVec15[i2] & l2) != 0L);
        case 14:
            return ((jjbitVec16[i2] & l2) != 0L);
        case 15:
            return ((jjbitVec17[i2] & l2) != 0L);
        case 16:
            return ((jjbitVec18[i2] & l2) != 0L);
        case 17:
            return ((jjbitVec19[i2] & l2) != 0L);
        case 18:
            return ((jjbitVec20[i2] & l2) != 0L);
        case 19:
            return ((jjbitVec21[i2] & l2) != 0L);
        case 20:
            return ((jjbitVec0[i2] & l2) != 0L);
        case 22:
            return ((jjbitVec22[i2] & l2) != 0L);
        case 23:
            return ((jjbitVec23[i2] & l2) != 0L);
        case 24:
            return ((jjbitVec24[i2] & l2) != 0L);
        case 30:
            return ((jjbitVec25[i2] & l2) != 0L);
        case 31:
            return ((jjbitVec26[i2] & l2) != 0L);
        case 32:
            return ((jjbitVec27[i2] & l2) != 0L);
        case 33:
            return ((jjbitVec28[i2] & l2) != 0L);
        case 48:
            return ((jjbitVec29[i2] & l2) != 0L);
        case 49:
            return ((jjbitVec30[i2] & l2) != 0L);
        case 77:
            return ((jjbitVec31[i2] & l2) != 0L);
        case 159:
            return ((jjbitVec32[i2] & l2) != 0L);
        case 164:
            return ((jjbitVec33[i2] & l2) != 0L);
        case 215:
            return ((jjbitVec34[i2] & l2) != 0L);
        case 250:
            return ((jjbitVec35[i2] & l2) != 0L);
        case 251:
            return ((jjbitVec36[i2] & l2) != 0L);
        case 253:
            return ((jjbitVec37[i2] & l2) != 0L);
        case 254:
            return ((jjbitVec38[i2] & l2) != 0L);
        case 255:
            return ((jjbitVec39[i2] & l2) != 0L);
        default:
            return (jjbitVec3[i1] & l1) != 0L;
        }
    }

    private static final boolean jjCanMove_2(int hiByte, int i1, int i2, long l1, long l2) {
        switch (hiByte) {
        case 0:
            return ((jjbitVec40[i2] & l2) != 0L);
        case 2:
            return ((jjbitVec5[i2] & l2) != 0L);
        case 3:
            return ((jjbitVec41[i2] & l2) != 0L);
        case 4:
            return ((jjbitVec42[i2] & l2) != 0L);
        case 5:
            return ((jjbitVec43[i2] & l2) != 0L);
        case 6:
            return ((jjbitVec44[i2] & l2) != 0L);
        case 7:
            return ((jjbitVec45[i2] & l2) != 0L);
        case 9:
            return ((jjbitVec46[i2] & l2) != 0L);
        case 10:
            return ((jjbitVec47[i2] & l2) != 0L);
        case 11:
            return ((jjbitVec48[i2] & l2) != 0L);
        case 12:
            return ((jjbitVec49[i2] & l2) != 0L);
        case 13:
            return ((jjbitVec50[i2] & l2) != 0L);
        case 14:
            return ((jjbitVec51[i2] & l2) != 0L);
        case 15:
            return ((jjbitVec52[i2] & l2) != 0L);
        case 16:
            return ((jjbitVec53[i2] & l2) != 0L);
        case 17:
            return ((jjbitVec19[i2] & l2) != 0L);
        case 18:
            return ((jjbitVec20[i2] & l2) != 0L);
        case 19:
            return ((jjbitVec54[i2] & l2) != 0L);
        case 20:
            return ((jjbitVec0[i2] & l2) != 0L);
        case 22:
            return ((jjbitVec22[i2] & l2) != 0L);
        case 23:
            return ((jjbitVec55[i2] & l2) != 0L);
        case 24:
            return ((jjbitVec56[i2] & l2) != 0L);
        case 30:
            return ((jjbitVec25[i2] & l2) != 0L);
        case 31:
            return ((jjbitVec26[i2] & l2) != 0L);
        case 32:
            return ((jjbitVec57[i2] & l2) != 0L);
        case 33:
            return ((jjbitVec28[i2] & l2) != 0L);
        case 48:
            return ((jjbitVec58[i2] & l2) != 0L);
        case 49:
            return ((jjbitVec30[i2] & l2) != 0L);
        case 77:
            return ((jjbitVec31[i2] & l2) != 0L);
        case 159:
            return ((jjbitVec32[i2] & l2) != 0L);
        case 164:
            return ((jjbitVec33[i2] & l2) != 0L);
        case 215:
            return ((jjbitVec34[i2] & l2) != 0L);
        case 250:
            return ((jjbitVec35[i2] & l2) != 0L);
        case 251:
            return ((jjbitVec59[i2] & l2) != 0L);
        case 253:
            return ((jjbitVec37[i2] & l2) != 0L);
        case 254:
            return ((jjbitVec60[i2] & l2) != 0L);
        case 255:
            return ((jjbitVec61[i2] & l2) != 0L);
        default:
            return (jjbitVec3[i1] & l1) != 0L;
        }
    }

    static public void ReInit(JavaCharStream stream) {
        jjmatchedPos = jjnewStateCnt = 0;
        curLexState = defaultLexState;
        input_stream = stream;
        ReInitRounds();
    }

    static private final void ReInitRounds() {
        int i;
        jjround = 0x80000001;
        for (i = 52; i-- > 0;) {
            jjrounds[i] = 0x80000000;
        }
    }

    static public void ReInit(JavaCharStream stream, int lexState) {
        ReInit(stream);
        SwitchTo(lexState);
    }

    static public void SwitchTo(int lexState) {
        if (lexState >= 4 || lexState < 0) {
            throw new TokenMgrError(
                "Error: Ignoring invalid lexical state : " + lexState + ". State unchanged.",
                TokenMgrError.INVALID_LEXICAL_STATE);
        } else {
            curLexState = lexState;
        }
    }

    static protected Token jjFillToken() {
        Token t = Token.newToken(jjmatchedKind);
        t.kind = jjmatchedKind;
        String im = jjstrLiteralImages[jjmatchedKind];
        t.image = (im == null) ? JavaCharStream.GetImage() : im;
        t.beginLine = JavaCharStream.getBeginLine();
        t.beginColumn = JavaCharStream.getBeginColumn();
        t.endLine = JavaCharStream.getEndLine();
        t.endColumn = JavaCharStream.getEndColumn();
        return t;
    }

    public static Token getNextToken() {
        int kind;
        Token specialToken = null;
        Token matchedToken;
        int curPos = 0;

        EOFLoop: for (;;) {
            try {
                curChar = JavaCharStream.BeginToken();
            } catch (java.io.IOException e) {
                jjmatchedKind = 0;
                matchedToken = jjFillToken();
                matchedToken.specialToken = specialToken;
                return matchedToken;
            }
            image = null;
            jjimageLen = 0;

            for (;;) {
                switch (curLexState) {
                case 0:
                    try {
                        JavaCharStream.backup(0);
                        while (curChar <= 32 && (0x100003600L & (1L << curChar)) != 0L) {
                            curChar = JavaCharStream.BeginToken();
                        }
                    } catch (java.io.IOException e1) {
                        continue EOFLoop;
                    }
                    jjmatchedKind = 0x7fffffff;
                    jjmatchedPos = 0;
                    curPos = jjMoveStringLiteralDfa0_0();
                    break;
                case 1:
                    jjmatchedKind = 0x7fffffff;
                    jjmatchedPos = 0;
                    curPos = jjMoveStringLiteralDfa0_1();
                    if (jjmatchedPos == 0 && jjmatchedKind > 12) {
                        jjmatchedKind = 12;
                    }
                    break;
                case 2:
                    jjmatchedKind = 0x7fffffff;
                    jjmatchedPos = 0;
                    curPos = jjMoveStringLiteralDfa0_2();
                    if (jjmatchedPos == 0 && jjmatchedKind > 12) {
                        jjmatchedKind = 12;
                    }
                    break;
                case 3:
                    jjmatchedKind = 0x7fffffff;
                    jjmatchedPos = 0;
                    curPos = jjMoveStringLiteralDfa0_3();
                    if (jjmatchedPos == 0 && jjmatchedKind > 12) {
                        jjmatchedKind = 12;
                    }
                    break;
                }
                if (jjmatchedKind != 0x7fffffff) {
                    if (jjmatchedPos + 1 < curPos) {
                        JavaCharStream.backup(curPos - jjmatchedPos - 1);
                    }
                    if ((jjtoToken[jjmatchedKind >> 6] & (1L << (jjmatchedKind & 077))) != 0L) {
                        matchedToken = jjFillToken();
                        matchedToken.specialToken = specialToken;
                        TokenLexicalActions(matchedToken);
                        if (jjnewLexState[jjmatchedKind] != -1) {
                            curLexState = jjnewLexState[jjmatchedKind];
                        }
                        return matchedToken;
                    } else if ((jjtoSkip[jjmatchedKind >> 6]
                            & (1L << (jjmatchedKind & 077))) != 0L) {
                        if ((jjtoSpecial[jjmatchedKind >> 6]
                                & (1L << (jjmatchedKind & 077))) != 0L) {
                            matchedToken = jjFillToken();
                            if (specialToken == null) {
                                specialToken = matchedToken;
                            } else {
                                matchedToken.specialToken = specialToken;
                                specialToken = (specialToken.next = matchedToken);
                            }
                            SkipLexicalActions(matchedToken);
                        } else {
                            SkipLexicalActions(null);
                        }
                        if (jjnewLexState[jjmatchedKind] != -1) {
                            curLexState = jjnewLexState[jjmatchedKind];
                        }
                        continue EOFLoop;
                    }
                    MoreLexicalActions();
                    if (jjnewLexState[jjmatchedKind] != -1) {
                        curLexState = jjnewLexState[jjmatchedKind];
                    }
                    curPos = 0;
                    jjmatchedKind = 0x7fffffff;
                    try {
                        curChar = JavaCharStream.readChar();
                        continue;
                    } catch (java.io.IOException e1) {
                    }
                }
                int error_line = JavaCharStream.getEndLine();
                int error_column = JavaCharStream.getEndColumn();
                String error_after = null;
                boolean EOFSeen = false;
                try {
                    JavaCharStream.readChar();
                    JavaCharStream.backup(1);
                } catch (java.io.IOException e1) {
                    EOFSeen = true;
                    error_after = curPos <= 1 ? "" : JavaCharStream.GetImage();
                    if (curChar == '\n' || curChar == '\r') {
                        error_line++;
                        error_column = 0;
                    } else {
                        error_column++;
                    }
                }
                if (!EOFSeen) {
                    JavaCharStream.backup(1);
                    error_after = curPos <= 1 ? "" : JavaCharStream.GetImage();
                }
                throw new TokenMgrError(EOFSeen, curLexState, error_line, error_column, error_after,
                    curChar, TokenMgrError.LEXICAL_ERROR);
            }
        }
    }

    static void SkipLexicalActions(Token matchedToken) {
        switch (jjmatchedKind) {
        case 9:
            if (image == null) {
                image = new StringBuffer();
            }
            image.append(JavaCharStream.GetSuffix(jjimageLen + (lengthOfMatch = jjmatchedPos + 1)));
            JavaCCParser.addSingleLineComment(matchedToken);
            break;
        case 10:
            if (image == null) {
                image = new StringBuffer();
            }
            image.append(JavaCharStream.GetSuffix(jjimageLen + (lengthOfMatch = jjmatchedPos + 1)));
            JavaCCParser.addDocComment(matchedToken);
            break;
        case 11:
            if (image == null) {
                image = new StringBuffer();
            }
            image.append(JavaCharStream.GetSuffix(jjimageLen + (lengthOfMatch = jjmatchedPos + 1)));
            JavaCCParser.addMultiLineComment(matchedToken);
            break;
        default:
            break;
        }
    }

    static void MoreLexicalActions() {
        jjimageLen += (lengthOfMatch = jjmatchedPos + 1);
        switch (jjmatchedKind) {
        case 7:
            if (image == null) {
                image = new StringBuffer();
            }
            image.append(JavaCharStream.GetSuffix(jjimageLen));
            jjimageLen = 0;
            JavaCharStream.backup(1);
            break;
        default:
            break;
        }
    }

    static void TokenLexicalActions(Token matchedToken) {
        switch (jjmatchedKind) {
        case 14:
            if (image == null) {
                image = new StringBuffer();
            }
            image.append(jjstrLiteralImages[14]);
            if (!JavaCCParser.jdk1_4) {
                matchedToken.kind = IDENTIFIER;
            }
            break;
        case 15:
            if (image == null) {
                image = new StringBuffer();
            }
            image.append(jjstrLiteralImages[15]);
            if (!JavaCCParser.jdk1_5) {
                // TODO
            }
            break;
        case 29:
            if (image == null) {
                image = new StringBuffer();
            }
            image.append(jjstrLiteralImages[29]);
            if (!JavaCCParser.jdk1_5) {
                matchedToken.kind = IDENTIFIER;
            }
            break;
        case 122:
            if (image == null) {
                image = new StringBuffer();
            }
            image.append(jjstrLiteralImages[122]);
            matchedToken.kind = GT;
            ((Token.GTToken) matchedToken).realKind = RUNSIGNEDSHIFT;
            JavaCharStream.backup(2);
            matchedToken.image = ">";
            break;
        case 123:
            if (image == null) {
                image = new StringBuffer();
            }
            image.append(jjstrLiteralImages[123]);
            matchedToken.kind = GT;
            ((Token.GTToken) matchedToken).realKind = RSIGNEDSHIFT;
            JavaCharStream.backup(1);
            matchedToken.image = ">";
            break;
        default:
            break;
        }
    }
}
