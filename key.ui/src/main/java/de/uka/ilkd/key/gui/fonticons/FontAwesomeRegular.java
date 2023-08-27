/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.fonticons;

import java.awt.*;
import java.io.IOException;

public enum FontAwesomeRegular implements IconFont {
    ADDRESS_BOOK('\uf2b9'), ADDRESS_CARD('\uf2bb'), ANGRY('\uf556'),
    ARROW_ALT_CIRCLE_DOWN('\uf358'), ARROW_ALT_CIRCLE_LEFT('\uf359'),
    ARROW_ALT_CIRCLE_RIGHT('\uf35a'), ARROW_ALT_CIRCLE_UP('\uf35b'), BELL('\uf0f3'),
    BELL_SLASH('\uf1f6'), BOOKMARK('\uf02e'), BUILDING('\uf1ad'), CALENDAR('\uf133'),
    CALENDAR_ALT('\uf073'), CALENDAR_CHECK('\uf274'), CALENDAR_MINUS('\uf272'),
    CALENDAR_PLUS('\uf271'), CALENDAR_TIMES('\uf273'), CARET_SQUARE_DOWN('\uf150'),
    CARET_SQUARE_LEFT('\uf191'), CARET_SQUARE_RIGHT('\uf152'), CARET_SQUARE_UP('\uf151'),
    CHART_BAR('\uf080'), CHECK_CIRCLE('\uf058'), CHECK_SQUARE('\uf14a'), CIRCLE('\uf111'),
    CLIPBOARD('\uf328'), CLOCK('\uf017'), CLONE('\uf24d'), CLOSED_CAPTIONING('\uf20a'),
    COMMENT('\uf075'), COMMENT_ALT('\uf27a'), COMMENT_DOTS('\uf4ad'), COMMENTS('\uf086'),
    COMPASS('\uf14e'), COPY('\uf0c5'), COPYRIGHT('\uf1f9'), CREDIT_CARD('\uf09d'), DIZZY('\uf567'),
    DOT_CIRCLE('\uf192'), EDIT('\uf044'), ENVELOPE('\uf0e0'), ENVELOPE_OPEN('\uf2b6'),
    EYE('\uf06e'), EYE_SLASH('\uf070'), FILE('\uf15b'), FILE_ALT('\uf15c'), FILE_ARCHIVE('\uf1c6'),
    FILE_AUDIO('\uf1c7'), FILE_CODE('\uf1c9'), FILE_EXCEL('\uf1c3'), FILE_IMAGE('\uf1c5'),
    FILE_PDF('\uf1c1'), FILE_POWERPOINT('\uf1c4'), FILE_VIDEO('\uf1c8'), FILE_WORD('\uf1c2'),
    FLAG('\uf024'), FLUSHED('\uf579'), FOLDER('\uf07b'), FOLDER_OPEN('\uf07c'),
    FONT_AWESOME_LOGO_FULL('\uf4e6'), FROWN('\uf119'), FROWN_OPEN('\uf57a'), FUTBOL('\uf1e3'),
    GEM('\uf3a5'), GRIMACE('\uf57f'), GRIN('\uf580'), GRIN_ALT('\uf581'), GRIN_BEAM('\uf582'),
    GRIN_BEAM_SWEAT('\uf583'), GRIN_HEARTS('\uf584'), GRIN_SQUINT('\uf585'),
    GRIN_SQUINT_TEARS('\uf586'), GRIN_STARS('\uf587'), GRIN_TEARS('\uf588'), GRIN_TONGUE('\uf589'),
    GRIN_TONGUE_SQUINT('\uf58a'), GRIN_TONGUE_WINK('\uf58b'), GRIN_WINK('\uf58c'),
    HAND_LIZARD('\uf258'), HAND_PAPER('\uf256'), HAND_PEACE('\uf25b'), HAND_POINT_DOWN('\uf0a7'),
    HAND_POINT_LEFT('\uf0a5'), HAND_POINT_RIGHT('\uf0a4'), HAND_POINT_UP('\uf0a6'),
    HAND_POINTER('\uf25a'), HAND_ROCK('\uf255'), HAND_SCISSORS('\uf257'), HAND_SPOCK('\uf259'),
    HANDSHAKE('\uf2b5'), HDD('\uf0a0'), HEART('\uf004'), HOSPITAL('\uf0f8'), HOURGLASS('\uf254'),
    ID_BADGE('\uf2c1'), ID_CARD('\uf2c2'), IMAGE('\uf03e'), IMAGES('\uf302'), KEYBOARD('\uf11c'),
    KISS('\uf596'), KISS_BEAM('\uf597'), KISS_WINK_HEART('\uf598'), LAUGH('\uf599'),
    LAUGH_BEAM('\uf59a'), LAUGH_SQUINT('\uf59b'), LAUGH_WINK('\uf59c'), LEMON('\uf094'),
    LIFE_RING('\uf1cd'), LIGHTBULB('\uf0eb'), LIST_ALT('\uf022'), MAP('\uf279'), MEH('\uf11a'),
    MEH_BLANK('\uf5a4'), MEH_ROLLING_EYES('\uf5a5'), MINUS_SQUARE('\uf146'),
    MONEY_BILL_ALT('\uf3d1'), MOON('\uf186'), NEWSPAPER('\uf1ea'), OBJECT_GROUP('\uf247'),
    OBJECT_UNGROUP('\uf248'), PAPER_PLANE('\uf1d8'), PAUSE_CIRCLE('\uf28b'), PLAY_CIRCLE('\uf144'),
    PLUS_SQUARE('\uf0fe'), QUESTION_CIRCLE('\uf059'), REGISTERED('\uf25d'), SAD_CRY('\uf5b3'),
    SAD_TEAR('\uf5b4'), SAVE('\uf0c7'), SHARE_SQUARE('\uf14d'), SMILE('\uf118'),
    SMILE_BEAM('\uf5b8'), SMILE_WINK('\uf4da'), SNOWFLAKE('\uf2dc'), SQUARE('\uf0c8'),
    STAR('\uf005'), STAR_HALF('\uf089'), STICKY_NOTE('\uf249'), STOP_CIRCLE('\uf28d'),
    SUN('\uf185'), SURPRISE('\uf5c2'), THUMBS_DOWN('\uf165'), THUMBS_UP('\uf164'),
    TIMES_CIRCLE('\uf057'), TIRED('\uf5c8'), TRASH_ALT('\uf2ed'), USER('\uf007'),
    USER_CIRCLE('\uf2bd'), WINDOW_CLOSE('\uf410'), WINDOW_MAXIMIZE('\uf2d0'),
    WINDOW_MINIMIZE('\uf2d1'), WINDOW_RESTORE('\uf2d2');

    private static Font font;
    private final char unicode;

    FontAwesomeRegular(char c) {
        unicode = c;
    }

    @Override
    public Font getFont() throws IOException, FontFormatException {
        if (font == null) {
            font = Font.createFont(Font.TRUETYPE_FONT,
                getClass().getResourceAsStream("/fonts/Font Awesome 6 Free-Regular-400.otf"));
        }
        return font;
    }

    @Override
    public char getUnicode() {
        return unicode;
    }
}
