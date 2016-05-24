/*
** Copyright (C) 2008 José Vander Meulen <jose.vandermeulen@uclouvain.be>
**
** This program is free software; you can redistribute it and/or modify
** it under the terms of the GNU General Public License as published by
** the Free Software Foundation; either version 2 of the License, or
** (at your option) any later version.
**
** This program is distributed in the hope that it will be useful,
** but WITHOUT ANY WARRANTY; without even the implied warranty of
** MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
** GNU General Public License for more details.
**
** You should have received a copy of the GNU General Public License
** along with this program; if not, write to the Free Software
** Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.
*/
package bank;

/**
 * A bank account. It is composed of:
 *  - an id number, and
 *  - a balance which is the amount of money held by this account.
 *
 * The id number is immutable. The balance is always at least 0.
 */
public final class Account {

    private static int counter = 0;

    // The balance of this account.  INVARIANT: always at least 0.
    private int balance;

    // The id number of this account.
    private final int id = counter++;

    /**
     * Create a new account with a unique id and a balance of "initialAmount".
     */
    public Account(final int initialAmount) {
        assert 0 <= initialAmount;
        balance = initialAmount;
    }

    /**
     * Returns the current balance.
     * Does not modify the state.
     */
    public int balance() {
        synchronized (this) {
            return balance;
        }
    }

    /**
     * Returns the id number.
     * Does not modify the state.
     */
    public int id() {
        return id;
    }

    /**
     * Withdraws money from the account.  Substracts "amount" from the current balance.
     *
     * PRECONDITION: the balance of this account is at least amount.
     */
    private void withdraw(final int amount) {
        assert 0 <= balance - amount;
        balance = balance - amount;
    }

    /**
     * Deposit money on the account.  Adds "amount" to the current balance.
     */
    private void deposit(final int amount) {
        assert 0 <= balance + amount;
        balance = balance + amount;
    }

    /**
     * Transfers up to "amount" from this account to the "other" account.
     * If the balance is lower than "amount", transfer the balance.
     * Synchronized on both accounts.
     */
    public int transferTo(final Account other, final int amount) {
        synchronized (getFirstSync(other)) {
            synchronized (getSecondSync(other)) {
                final int initialSum = this.balance() + other.balance();
                final int maxAmount = Math.min(balance, amount);
                withdraw(maxAmount);
                other.deposit(maxAmount);
                assert initialSum == this.balance() + other.balance();
                return maxAmount;
            }
        }
    }
    private Account getFirstSync(Account other) {
        if (this.id() < other.id()) return this;
        else return other;
    }
    private Account getSecondSync(Account other) {
        if (this.id() > other.id()) return this;
        else return other;
    }

    /**
     * Merges current balance of "other" account into this account.
     * Sets the balance of "other" to zero.
     */
    public void merge(final Account other) {
        synchronized (getFirstSync(other)) {
            synchronized (getSecondSync(other)) {
                this.balance = this.balance + other.balance;
                other.balance = 0;
            }
        }
    }

}
