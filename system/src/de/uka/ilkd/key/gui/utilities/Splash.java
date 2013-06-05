package de.uka.ilkd.key.gui.utilities;

import java.awt.Frame;
import java.awt.Graphics2D;
import java.awt.SplashScreen;

/** Display a simple splash screen while KeY is loading.
 *
 * @author bruns
 */
public class Splash extends Frame {

    private Splash() {
        Graphics2D g = SplashScreen.getSplashScreen().createGraphics();
    }


    public static void main(String[] a) {
    }
}
