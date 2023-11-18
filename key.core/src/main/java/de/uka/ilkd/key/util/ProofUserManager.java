/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.util;

import java.util.HashSet;
import java.util.Set;
import java.util.WeakHashMap;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.proof.Proof;

/**
 * This singleton class is used to manage user of a {@link Proof} to make sure that a {@link Proof}
 * is only disposed via {@link Proof#dispose()} if it is no longer in use (no user available).
 *
 * @author Martin Hentschel
 */
public final class ProofUserManager {
    /**
     * Stores for each {@link Proof} the registered users.
     */
    private final WeakHashMap<Proof, Set<Object>> proofUsers =
        new WeakHashMap<>();

    /**
     * Stores for each {@link KeYEnvironment} the known {@link Proof}s.
     */
    private final WeakHashMap<KeYEnvironment<?>, Set<Proof>> environmentProofs =
        new WeakHashMap<>();

    /**
     * Stores for each {@link Proof} the {@link KeYEnvironment} it lives in..
     */
    private final WeakHashMap<Proof, KeYEnvironment<?>> proofEnvironments =
        new WeakHashMap<>();

    /**
     * The only instance of this class.
     */
    private static final ProofUserManager instance = new ProofUserManager();

    /**
     * Forbid multiple instances.
     */
    private ProofUserManager() {
    }

    /**
     * Registers the {@link Proof} with the given user if it is not already registered. If it is
     * already registered the user is added to the proof users if not already present.
     *
     * @param proof The {@link Proof}.
     * @param environment Optional the {@link KeYEnvironment} which will be disposed if the last
     *        known {@link Proof} is removed from it.
     * @param user The user.
     */
    public void addUser(Proof proof, KeYEnvironment<?> environment, Object user) {
        if (proof == null) {
            throw new IllegalArgumentException("Proof not defined.");
        }
        if (user == null) {
            throw new IllegalArgumentException("User not defined.");
        }
        synchronized (this) {
            Set<Object> users = proofUsers.computeIfAbsent(proof, k -> new HashSet<>());
            users.add(user);
            if (environment != null) {
                proofEnvironments.put(proof, environment);
                Set<Proof> proofs =
                    environmentProofs.computeIfAbsent(environment, k -> new HashSet<>());
                proofs.add(proof);
            }
        }
    }

    /**
     * Removes the user from the registered proof users. If the proof has no user anymore it is
     * automatically disposed via {@link Proof#dispose()}.
     *
     * @param proof The {@link Proof}.
     * @param user The user.
     */
    public void removeUserAndDispose(Proof proof, Object user) {
        if (proof == null) {
            throw new IllegalArgumentException("Proof not defined.");
        }
        if (user == null) {
            throw new IllegalArgumentException("User not defined.");
        }
        synchronized (this) {
            Set<Object> users = proofUsers.get(proof);
            if (users != null) {
                users.remove(user);
                if (users.isEmpty()) {
                    proofUsers.remove(proof);
                    KeYEnvironment<?> environment = proofEnvironments.remove(proof);
                    if (environment != null) {
                        proof.dispose();
                        Set<Proof> proofs = environmentProofs.get(environment);
                        if (proofs != null) {
                            proofs.remove(proof);
                            if (proofs.isEmpty()) {
                                environmentProofs.remove(environment);
                                environment.dispose();
                            }
                        }
                    } else {
                        proof.dispose();
                    }
                }
            } else {
                proof.dispose();
            }
        }
    }

    /**
     * Returns all registered {@link Proof}s.
     *
     * @return All registered {@link Proof}s.
     */
    public Proof[] getProofs() {
        synchronized (this) {
            Set<Proof> keys = proofUsers.keySet();
            return keys.toArray(new Proof[0]);
        }
    }

    /**
     * Returns all registered user of the given {@link Proof}.
     *
     * @param proof The {@link Proof} to get its users.
     * @return The registered user of the {@link Proof}.
     */
    public Object[] getUsers(Proof proof) {
        if (proof != null) {
            synchronized (this) {
                Set<Object> users = proofUsers.get(proof);
                return users != null ? users.toArray(new Object[0]) : new Object[0];
            }
        } else {
            return new Object[0];
        }
    }

    /**
     * Returns the known environment of the given {@link Proof}.
     *
     * @param proof The {@link Proof} to get its {@link KeYEnvironment}.
     * @return The {@link KeYEnvironment} of the given {@link Proof}.
     */
    public KeYEnvironment<?> getEnvironment(Proof proof) {
        if (proof != null) {
            synchronized (this) {
                return proofEnvironments.get(proof);
            }
        } else {
            return null;
        }
    }

    /**
     * Returns all known {@link Proof}s of the given {@link KeYEnvironment}.
     *
     * @param environment The known {@link Proof}s of the given {@link KeYEnvironment}.
     * @return All known {@link Proof}s of the given {@link KeYEnvironment}.
     */
    public Proof[] getProofs(KeYEnvironment<?> environment) {
        if (environment != null) {
            synchronized (this) {
                Set<Proof> proofs = environmentProofs.get(environment);
                return proofs != null ? proofs.toArray(new Proof[0]) : new Proof[0];
            }
        } else {
            return new Proof[0];
        }
    }

    /**
     * Returns the singleton instance of this class.
     *
     * @return The singleton instance of this class.
     */
    public static ProofUserManager getInstance() {
        return instance;
    }
}
