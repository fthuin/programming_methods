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

import java.util.Random;
import java.util.ArrayList;
import java.util.List;

public class TestHarness {

    private static final Random random = new Random();

    /**
     * A test run with "nbrOfTrans" concurrent transfers between
     * randomly selected accounts among "nbrOfAccount".  Initial account balances
     * are randomly picked in "1..maxInitAmount" and transfer amounts are randomly
     * picked in "1..maxTransferAmount".
     */
    public static void concurrentTransactions(
            final int nbrOfTransfer,
            final int nbrOfAccount,
            final int maxInitAmount,
            final int maxTransferAmount) {

        final Account[] accounts = new Account[nbrOfAccount];

        int i = 0;
        while (i != accounts.length) {
            accounts[i] = new Account(random.nextInt(maxInitAmount) + 1);
            i = i + 1;
        }

        i = 0;
        while (i != nbrOfTransfer) {
            final Thread t = new Thread() {
                @Override
                public void run() {
                    final Account a1 = accounts[random.nextInt(accounts.length)];
                    final Account a2 = accounts[random.nextInt(accounts.length)];
                    final int amount = random.nextInt(maxTransferAmount) + 1;
                    a1.transferTo(a2, amount);
                }
            };
            t.start();
            i = i + 1;
        }

        // Uncomment to see the merge tests
        /*
        i = 0;
        while (i != nbrOfTransfer) {
            final Thread t = new Thread() {
                @Override
                public void run() {
                    final Account a1 = accounts[random.nextInt(accounts.length)];
                    final Account a2 = accounts[random.nextInt(accounts.length)];
                    if (a1.id() != a2.id()) a1.merge(a2);
                }
            };
            t.start();
            i = i + 1;
        }
        */
    }

    /**
     * Start test with chosen parameters.
     */
    public static void main(String[] args) {
        concurrentTransactions(3, 3, 20, 10);
    }
}
