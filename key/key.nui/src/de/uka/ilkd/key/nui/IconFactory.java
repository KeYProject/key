// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.nui;

import java.io.InputStream;
import java.net.URISyntaxException;
import java.net.URL;

import javafx.scene.image.Image;

public class IconFactory {

	private IconFactory() {
	}

	private static Image keyHole = getImage("images/ekey-mono.gif");
	private static Image keyHoleAlmostClosed = getImage("images/ekey-brackets.gif");
	private static Image keyHoleClosed = getImage("images/keyproved.gif");
	private static Image keyHoleInteractive = getImage("images/keyinteractive.gif");
	private static Image keyHoleLinked = getImage("images/keylinked.gif");
	private static Image keyLogo = getImage("images/key-color.gif");
	private static Image keyLogo22 = getImage("images/key22.gif");
	private static Image keyLogoSmall = getImage("images/key-color-icon-square.png");

	private static Image oneStepSimplifier = getImage("images/toolbar/oneStepSimplifier.png");

	private static Image prune = getImage("images/toolbar/pruneProof.png");
	private static Image goalBack = getImage("images/toolbar/goalBack.png");
	private static Image autoModeStart = getImage("images/toolbar/autoModeStart.png");
	private static Image autoModeStop = getImage("images/toolbar/autoModeStop.png");
	private static Image decisionProcedureConfigArrow = getImage("images/toolbar/decProcArrow.png");

	private static Image junit = getImage("images/toolbar/junit_logo.png");
	private static Image jml = getImage("images/toolbar/jml.png");
	private static Image uml = getImage("images/toolbar/uml.png");

	private static Image openKeYFile = getImage("images/toolbar/open.png");
	private static Image openMostRecentKeYFile = getImage("images/toolbar/openMostRecent.png");
	private static Image saveFile = getImage("images/toolbar/saveFile.png");
	private static Image editFile = getImage("images/toolbar/edit.png");
	private static Image abandonProof = getImage("images/toolbar/abandon.png");
	private static Image configure = getImage("images/toolbar/config.png");
	private static Image help = getImage("images/toolbar/help.png");
	private static Image proofMgt = getImage("images/toolbar/mgt.png");
	private static Image properties = getImage("images/toolbar/properties.png");
	private static Image quit = getImage("images/toolbar/quit.png");
	private static Image recentFiles = getImage("images/toolbar/recent.png");
	private static Image search = getImage("images/toolbar/search.png");
	private static Image search2 = getImage("images/toolbar/search2.png");
	private static Image statistics = getImage("images/toolbar/statistics.png");
	private static Image toolbox = getImage("images/toolbar/toolbox.png");

	private static Image plus = getImage("images/toolbar/plus.png");
	private static Image minus = getImage("images/toolbar/minus.png");
	private static Image expandGoals = getImage("images/toolbar/expandGoals.png");

	private static Image next = getImage("images/toolbar/go-next.png");
	private static Image previous = getImage("images/toolbar/go-previous.png");
	private static Image stop = getImage("images/toolbar/stop.png");

	private static Image interactiveAppLogo = getImage("images/interactiveAppLogo.png");

	private static Image counterexampleImage = getImage("images/toolbar/ce.png");
	private static Image testgenerationImage = getImage("images/toolbar/tg.png");

	private static Image getImage(String string) {
		InputStream is = IconFactory.class.getClass().getResourceAsStream("keyproved.gif");
		InputStream is2 = IconFactory.class.getClass().getResourceAsStream("resources/images/keyproved.gif");

		InputStream is3 = IconFactory.class.getClassLoader().getResourceAsStream("/keyproved.gif");
		InputStream is4 = IconFactory.class.getClassLoader().getResourceAsStream("resources/images/keyproved.gif");
		InputStream is5 = IconFactory.class.getClassLoader().getResourceAsStream("keyproved.gif");
		InputStream is6 = IconFactory.class.getClassLoader().getResourceAsStream("key.nui/resources/images/keyproved.gif");
		String url = IconFactory.class.getResource("").getPath();
		System.out.println(IconFactory.class.getClass().toGenericString());
		if (is == null) {
			System.out.println("INPUTSTREAM is NULL");
			System.exit(0);
		}
		Image img = new Image(is, 20, 20, true, true);
		return img;
//		String resourceURL = String.valueOf(IconFactory.class.getResource(string));
//		Image img = new Image(resourceURL, true);
//		System.out.println(resourceURL);
//		return img;
		//return new Image(resourceURL, 20, 20, true, true);
	}

	public static Image getKeyHoleClosed() {
		return keyHoleClosed;
	}

}

