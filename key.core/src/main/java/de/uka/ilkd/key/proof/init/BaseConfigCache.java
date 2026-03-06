/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.init;

import java.io.IOException;
import java.nio.ByteBuffer;
import java.nio.file.Files;
import java.nio.file.Path;
import java.security.MessageDigest;
import java.util.Collection;
import java.util.stream.Stream;

import de.uka.ilkd.key.proof.io.EnvInput;

import org.jspecify.annotations.NonNull;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Caches the base input config for a given classpath digest. This allows to reuse the base input
 * config
 * across multiple proof runs, as long as the classpath does not change.
 *
 * The bootclasspath is also taken into account for the digest -- but the builtin REDUX classes are
 * not
 * digested as not needed.
 *
 * This is only used in {@link ProblemInitializer#createInputConfigFor(EnvInput)}.
 *
 * @author Mattias Ulbrich
 * @see ProblemInitializer
 */
class BaseConfigCache {

    private static final Logger LOGGER = LoggerFactory.getLogger(BaseConfigCache.class);

    /** Special value used for no classpath config */
    private static final byte[] VALUE_FOR_EMPTY = new byte[0];

    /** Special value used instead of parsing the redux classes */
    private static final byte[] VALUE_FOR_REDUX_CLASSES =
        "Placeholder for reading REDUX classes".getBytes();

    /** The cached instance */
    private static InitConfig baseInputConfig;

    /** The digest of the classpath that was used to create the cached instance */
    private static byte[] baseInputConfigHash;

    private BaseConfigCache() {
        // prevent instantiation
        throw new UnsupportedOperationException("This class cannot be instantiated");
    }

    /**
     * Updates the given message digest with the content of the given path. If the path is a
     * directory, all files in the directory are also digested.
     *
     * @param md the message digest to update
     * @param path the path to digest
     */
    private static void digestPath(@NonNull MessageDigest md, @NonNull Path path) {
        try {
            if (Files.isDirectory(path)) {
                try (Stream<Path> walker = Files.walk(path)) {
                    walker.sorted().forEach(it -> {
                        if (!it.equals(path))
                            digestPath(md, it);
                    });
                } catch (IOException e) {
                    LOGGER.warn("Failed to read file: {}", path, e);
                }
            } else {
                try (var channel = Files.newByteChannel(path)) {
                    ByteBuffer bytes = ByteBuffer.allocate((int) channel.size());
                    channel.read(bytes);
                    md.update(bytes);
                }
            }
        } catch (IOException e) {
            LOGGER.warn("Failed to read file: {}", path, e);
        }
    }

    /**
     * Computes a digest for the classpath in the given environment input.
     * This includes both the classpath and the bootclasspath, but does not read the builtin REDUX
     * classes.
     * This allows reusing the cached config across multiple proof runs, as long as the classpath
     * does not change.
     *
     * The digest is computed by hashing the content of all files in the classpath and the
     * bootclasspath (if present).
     * The order of the files does not matter, as they are sorted before hashing.
     * If both classpath and bootclasspath are empty, a special value is returned.
     *
     * @param envInput the environment input to read the classpath from
     * @return the computed digest, or null if an error occurred while reading the classpath
     */
    public static @NonNull byte[] computeClasspathDigest(@NonNull EnvInput envInput) {
        Path bootclasspath = envInput.readBootClassPath();
        Collection<Path> classpath = envInput.readClassPath();

        if (classpath.isEmpty() && bootclasspath == null) {
            return VALUE_FOR_EMPTY;
        }

        try {
            var totalHash = MessageDigest.getInstance("SHA-256");
            classpath.stream().sorted().forEach(path -> digestPath(totalHash, path));
            if (bootclasspath != null) {
                digestPath(totalHash, bootclasspath);
            } else {
                totalHash.digest(VALUE_FOR_REDUX_CLASSES);
            }
            return totalHash.digest();
        } catch (Exception e) {
            LOGGER.error("Error while computing hash for classpaths (for caching init configs)", e);
            return null;
        }
    }


    public static boolean matchesCachedConfig(Profile profile, byte[] inputDigest) {
        if (baseInputConfig == null) {
            return false;
        }
        if (!MessageDigest.isEqual(baseInputConfigHash, inputDigest)) {
            return false;
        }
        if (profile != baseInputConfig.getProfile()) {
            return false;
        }
        return true;
    }

    /**
     * Returns the cached base input config. This should only be called if
     * {@link #matchesCachedConfig(Profile, byte[])} returns true.
     *
     * @return the cached base input config
     * @throws IllegalStateException if no cached config is available
     */
    public static @NonNull InitConfig getBaseInputConfig() {
        if (baseInputConfig == null) {
            throw new IllegalStateException("No cached config available");
        }
        return baseInputConfig;
    }

    /**
     * Update the cache with the given config and input digest. Config and digest *must* be
     * consistent with each other, i.e., the digest must be the result of calling
     * {@link #computeClasspathDigest(EnvInput)} on an environment input that would lead to the
     * given config.
     *
     * @param config the config to cache
     * @param inputDigest the digest of the classpath of config.
     */
    public static void setBaseInputConfig(@NonNull InitConfig config, byte[] inputDigest) {
        baseInputConfig = config;
        baseInputConfigHash = inputDigest;
    }
}
