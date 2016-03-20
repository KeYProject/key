package de.uka.ilkd.key.nui.tests.guitests;

import org.testfx.api.FxRobot;
import javafx.scene.input.KeyCode;

/**
 * This class provides additional features in dealing with JavaFX KeyCodes, see
 * {@link javafx.scene.input.KeyCode}.
 * 
 * @author Patrick Jattke
 *
 */
public class KeyCodeHelper {

    /**
     * The {@link FxRobot} used to type in the {@link KeyCode KeyCodes}.
     */
    private FxRobot robot;

    /**
     * To use auto-type functionality the FxRobot {@link org.testfx.api.FxRobot}
     * must be provided. This is usually the test class extending
     * {@link org.loadui.testfx.GuiTest}.
     * 
     * @param robot
     *            The FxRobot of the test class.
     */
    public KeyCodeHelper(final FxRobot robot) {
        this.robot = robot;
    }

    /**
     * Takes a String as input parameter and returns an array consisting of
     * KeyCodes. The String must only consist of the following characters:
     * 
     * <pre>
     *  [0-9],[A-Z],[a-z], {.}, {,}, {/}, {" "}, {-}, {_}
     * </pre>
     * 
     * @param term
     *            The word which should be converted into an array of KeyCodes.
     * @return An array of KeyCodes representing the given word.
     */
    public KeyCode[] getKeyCode(final String term) {
        final KeyCode[] c = new KeyCode[term.length()];
        String current;
        for (int i = 0; i < term.length(); i++) {
            current = Character.toString(term.charAt(i));
            switch (current) {
            case ".":
                c[i] = KeyCode.PERIOD;
                break;
            case ",":
                c[i] = KeyCode.COMMA;
                break;
            case " ":
                c[i] = KeyCode.SPACE;
                break;
            case "/":
                c[i] = KeyCode.SLASH;
                break;
            case "_":
                c[i] = KeyCode.UNDERSCORE;
                break;
            case "-":
                c[i] = KeyCode.MINUS;
                break;
            default:
                c[i] = KeyCode.getKeyCode(current);
                break;
            }
        }
        return c;
    }

    /**
     * Types the given KeyCode array one per one.
     * 
     * @param keys
     *            The array consisting of key codes.
     */
    public void typeKeys(final KeyCode[] keys) {
        for (int i = 0; i < keys.length; i++) {
            if (keys[i] != null) {
                robot.type(keys[i]);
            }
        }
    }
}
