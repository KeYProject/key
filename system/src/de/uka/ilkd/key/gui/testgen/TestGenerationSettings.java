package de.uka.ilkd.key.gui.testgen;

import java.io.File;
import java.util.Collection;
import java.util.LinkedHashSet;
import java.util.Properties;

import de.uka.ilkd.key.gui.GUIEvent;
import de.uka.ilkd.key.gui.configuration.Settings;
import de.uka.ilkd.key.gui.configuration.SettingsConverter;
import de.uka.ilkd.key.gui.configuration.SettingsListener;

public class TestGenerationSettings implements Settings, Cloneable {
	// Default Values for option fields
	private static final int DEFAULT_MAXUNWINDS = 3;
	private static final int DEFAULT_CONCURRENTPROCESSES = 1;
	private static final String DEFAULT_OUTPUTPATH = System
	        .getProperty("user.home") + File.separator + "testFiles";
	private static final boolean DEFAULT_REMOVEDUPLICATES = true;
	private static final boolean DEFAULT_USERFL = false;
	private static final boolean DEFAULT_USEJUNIT = false;
	private static final boolean DEFAULT_INVARIANTFORALL = true;
	private static final String DEFAULT_OPENJMLPATH = "openjml";
	// Option fields
	private int maxUnwinds;
	private String outputPath;
	private String openjmlPath;
	private boolean removeDuplicates;
	private boolean useRFL;
	private boolean useJunit;
	private int concurrentProcesses;
	private boolean invariantForAll;
	private final Collection<SettingsListener> listeners;
	// Property name
	private static final String propMaxUwinds = "[TestGenSettings]maxUnwinds";
	private static final String propOutputPath = "[TestGenSettings]OutputPath";
	private static final String propRemoveDuplicates = "[TestGenSettings]RemoveDuplicates";
	private static final String propUseRFL = "[TestGenSettings]UseRFL";
	private static final String propUseJUnit = "[TestGenSettings]UseJUnit";
	private static final String propConcurrentProcesses = "[TestGenSettings]ConcurrentProcesses";
	private static final String propInvariantForAll = "[TestGenSettings]InvariantForAll";
	private static final String propOpenjmlPath = "[TestGenSettings]OpenJMLPath";
	public TestGenerationSettings() {
		listeners = new LinkedHashSet<SettingsListener>();
		maxUnwinds = TestGenerationSettings.DEFAULT_MAXUNWINDS;
		outputPath = TestGenerationSettings.DEFAULT_OUTPUTPATH;
		removeDuplicates = TestGenerationSettings.DEFAULT_REMOVEDUPLICATES;
		useRFL = TestGenerationSettings.DEFAULT_USERFL;
		useJunit = TestGenerationSettings.DEFAULT_USEJUNIT;
		concurrentProcesses = TestGenerationSettings.DEFAULT_CONCURRENTPROCESSES;
		invariantForAll = TestGenerationSettings.DEFAULT_INVARIANTFORALL;
		openjmlPath = DEFAULT_OPENJMLPATH;
	}

	public TestGenerationSettings(TestGenerationSettings data) {
		listeners = new LinkedHashSet<SettingsListener>();
		for (final SettingsListener l : data.listeners) {
			listeners.add(l);
		}
		maxUnwinds = data.maxUnwinds;
		outputPath = data.outputPath;
		removeDuplicates = data.removeDuplicates;
		useJunit = data.useJunit;
		useRFL = data.useRFL;
		concurrentProcesses = data.concurrentProcesses;
		invariantForAll = data.invariantForAll;
		openjmlPath = data.openjmlPath;
	}

	@Override
	public void addSettingsListener(SettingsListener l) {
		listeners.add(l);
	}

	public TestGenerationSettings clone(TestGenerationSettings data) {
		return new TestGenerationSettings(data);
	}

	public void fireSettingsChanged() {
		for (final SettingsListener aListenerList : listeners) {
			aListenerList.settingsChanged(new GUIEvent(this));
		}
	}

	public int getMaximalUnwinds() {
		return maxUnwinds;
	}

	public int getNumberOfProcesses() {
		return concurrentProcesses;
	}

	public String getOutputFolderPath() {
		return outputPath;
	}

	public boolean invaraiantForAll() {
		return invariantForAll;
	}

	@Override
	public void readSettings(Object sender, Properties props) {
		maxUnwinds = SettingsConverter.read(props,
		        TestGenerationSettings.propMaxUwinds,
		        TestGenerationSettings.DEFAULT_MAXUNWINDS);
		outputPath = SettingsConverter.read(props,
		        TestGenerationSettings.propOutputPath,
		        TestGenerationSettings.DEFAULT_OUTPUTPATH);
		removeDuplicates = SettingsConverter.read(props,
		        TestGenerationSettings.propRemoveDuplicates,
		        TestGenerationSettings.DEFAULT_REMOVEDUPLICATES);
		useRFL  = SettingsConverter.read(props,
		        TestGenerationSettings.propUseRFL,
		        TestGenerationSettings.DEFAULT_USERFL);
		useJunit = SettingsConverter.read(props,
		        TestGenerationSettings.propUseJUnit,
		        TestGenerationSettings.DEFAULT_USEJUNIT);
		concurrentProcesses = SettingsConverter.read(props,
		        TestGenerationSettings.propConcurrentProcesses,
		        TestGenerationSettings.DEFAULT_CONCURRENTPROCESSES);
		invariantForAll = SettingsConverter.read(props,
		        TestGenerationSettings.propInvariantForAll,
		        TestGenerationSettings.DEFAULT_INVARIANTFORALL);
		openjmlPath = SettingsConverter.read(props,
		        TestGenerationSettings.propOpenjmlPath,
		        TestGenerationSettings.DEFAULT_OPENJMLPATH);
	}

	public boolean removeDuplicates() {
		return removeDuplicates;
	}

	public void setConcurrentProcesses(int concurrentProcesses) {
		this.concurrentProcesses = concurrentProcesses;
	}

	public void setInvariantForAll(boolean invariantForAll) {
		this.invariantForAll = invariantForAll;
	}

	public void setMaxUnwinds(int maxUnwinds) {
		this.maxUnwinds = maxUnwinds;
	}

	public void setOutputPath(String outputPath) {
		this.outputPath = outputPath;
	}

	public void setRemoveDuplicates(boolean removeDuplicates) {
		this.removeDuplicates = removeDuplicates;
	}

	public void setRFL(boolean useRFL) {
		this.useRFL = useRFL;
	}

	public void setUseJunit(boolean useJunit) {
		this.useJunit = useJunit;
	}
	
	

	public String getOpenjmlPath() {
		return openjmlPath;
	}

	public void setOpenjmlPath(String openjmlPath) {
		this.openjmlPath = openjmlPath;
	}

	public boolean useRFL() {
		return useJunit;
	}

	public boolean useJunit() {
		return useJunit;
	}


	@Override
	public void writeSettings(Object sender, Properties props) {
		//System.out.println("Saving: "+maxUnwinds);
		SettingsConverter.store(props,
		        TestGenerationSettings.propConcurrentProcesses,
		        concurrentProcesses);
		SettingsConverter.store(props,
		        TestGenerationSettings.propInvariantForAll,
		        invariantForAll);
		SettingsConverter.store(props, TestGenerationSettings.propMaxUwinds,
		        maxUnwinds);
		SettingsConverter.store(props, TestGenerationSettings.propOutputPath,
		        outputPath);
		SettingsConverter.store(props,
		        TestGenerationSettings.propRemoveDuplicates,
		        removeDuplicates);
		SettingsConverter.store(props,
		        TestGenerationSettings.propUseRFL,
		        useRFL);
		SettingsConverter.store(props, TestGenerationSettings.propUseJUnit,
		        useJunit);
		SettingsConverter.store(props, TestGenerationSettings.propOpenjmlPath,
		        openjmlPath);
	}
}
