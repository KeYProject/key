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
	private static final boolean DEFAULT_USEJUNIT = false;
	private static final boolean DEFAULT_INVARIANTFORALL = true;
	// Option fields
	private int maxUnwinds;
	private String outputPath;
	private boolean removeDuplicates;
	private boolean useJunit;
	private int concurrentProcesses;
	private boolean invariantForAll;
	private final Collection<SettingsListener> listeners;
	// Property name
	private static final String propMaxUwinds = "[TestGenSettings]maxUnwinds";
	private static final String propOutputPath = "[TestGenSettings]OutputPath";
	private static final String propRemoveDuplicates = "[TestGenSettings]RemoveDuplicates";
	private static final String propUseJUnit = "[TestGenSettings]UseJUnit";
	private static final String propConcurrentProcesses = "[TestGenSettings]ConcurrentProcesses";
	private static final String propInvariantForAll = "[TestGenSettings]InvariantForAll";

	public TestGenerationSettings() {
		listeners = new LinkedHashSet<SettingsListener>();
		maxUnwinds = TestGenerationSettings.DEFAULT_MAXUNWINDS;
		outputPath = TestGenerationSettings.DEFAULT_OUTPUTPATH;
		removeDuplicates = TestGenerationSettings.DEFAULT_REMOVEDUPLICATES;
		useJunit = TestGenerationSettings.DEFAULT_USEJUNIT;
		concurrentProcesses = TestGenerationSettings.DEFAULT_CONCURRENTPROCESSES;
		invariantForAll = TestGenerationSettings.DEFAULT_INVARIANTFORALL;
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
		concurrentProcesses = data.concurrentProcesses;
		invariantForAll = data.invariantForAll;
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
		useJunit = SettingsConverter.read(props,
		        TestGenerationSettings.propUseJUnit,
		        TestGenerationSettings.DEFAULT_USEJUNIT);
		concurrentProcesses = SettingsConverter.read(props,
		        TestGenerationSettings.propConcurrentProcesses,
		        TestGenerationSettings.DEFAULT_CONCURRENTPROCESSES);
		invariantForAll = SettingsConverter.read(props,
		        TestGenerationSettings.propInvariantForAll,
		        TestGenerationSettings.DEFAULT_INVARIANTFORALL);
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

	public void setUseJunit(boolean useJunit) {
		this.useJunit = useJunit;
	}

	public boolean useJunit() {
		return useJunit;
	}

	@Override
	public void writeSettings(Object sender, Properties props) {
		SettingsConverter.store(props,
		        TestGenerationSettings.propConcurrentProcesses,
		        TestGenerationSettings.DEFAULT_CONCURRENTPROCESSES);
		SettingsConverter.store(props,
		        TestGenerationSettings.propInvariantForAll,
		        TestGenerationSettings.DEFAULT_INVARIANTFORALL);
		SettingsConverter.store(props, TestGenerationSettings.propMaxUwinds,
		        TestGenerationSettings.DEFAULT_MAXUNWINDS);
		SettingsConverter.store(props, TestGenerationSettings.propOutputPath,
		        TestGenerationSettings.DEFAULT_OUTPUTPATH);
		SettingsConverter.store(props,
		        TestGenerationSettings.propRemoveDuplicates,
		        TestGenerationSettings.DEFAULT_REMOVEDUPLICATES);
		SettingsConverter.store(props, TestGenerationSettings.propUseJUnit,
		        TestGenerationSettings.DEFAULT_USEJUNIT);
	}
}
