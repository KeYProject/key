package de.uka.ilkd.key.net;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.net.MalformedURLException;
import java.net.URL;
import java.net.UnknownHostException;


public final class NetworkUtils {

    private static final URL KEY_URL = getURL("http://key-project.org/");

    /**
     * Tests whether the KeY Project home page is
     * accessible over the internet.
     */
    public static boolean homePageAvailable() {
        BufferedReader in = null;
        try {
            final InputStreamReader isr = new InputStreamReader(KEY_URL.openStream());
            in = new BufferedReader(isr);
            in.close();
            return true;
        } catch (UnknownHostException e) {
            // this should usually happen
            return false;
        } catch (IOException e) {
            // something else (should not happen)
            e.printStackTrace();
            assert false;
            return false;
        } finally {
            if (in != null)
                try {
                    in.close();
                } catch (IOException e) {}
        }
    }
    
    /**
     * Create an URL without raising {@link MalformedURLException},
     * but {@link AssertionError} instead. Use with care.
     */
    public static URL getURL(String urlString) {
        try {
            return new URL(urlString);
        } catch (MalformedURLException e) {
            assert false;
            return null;
        }
    }
    
    public static void main(String[] a) {
        System.out.println(homePageAvailable());
    }
}
