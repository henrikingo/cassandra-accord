/*
 * Licensed to the Apache Software Foundation (ASF) under one
 * or more contributor license agreements.  See the NOTICE file
 * distributed with this work for additional information
 * regarding copyright ownership.  The ASF licenses this file
 * to you under the Apache License, Version 2.0 (the
 * "License"); you may not use this file except in compliance
 * with the License.  You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package accord.messages;

import javax.annotation.Nullable;

import accord.api.Key;
import accord.api.Result;
import accord.api.RoutingKey;
import accord.local.*;
import accord.local.Node.Id;
import accord.primitives.Ballot;
import accord.primitives.Timestamp;
import accord.primitives.TxnId;

import java.util.Collections;
import accord.primitives.*;
import accord.topology.Topologies;
import accord.utils.MapReduceConsume;

import static accord.local.SaveStatus.NotWitnessed;
import static accord.local.Status.*;
import static accord.local.Status.Durability.NotDurable;
import static accord.messages.TxnRequest.computeScope;

public class CheckStatus extends AbstractEpochRequest<CheckStatus.CheckStatusOk>
        implements EpochRequest, PreLoadContext, MapReduceConsume<SafeCommandStore, CheckStatus.CheckStatusOk>
{
    public static class SerializationSupport
    {
        public static CheckStatusOk createOk(SaveStatus status, Ballot promised, Ballot accepted, @Nullable Timestamp executeAt,
                                             boolean isCoordinating, Durability durability,
                                             @Nullable AbstractRoute route, @Nullable RoutingKey homeKey)
        {
            return new CheckStatusOk(status, promised, accepted, executeAt, isCoordinating, durability, route, homeKey);
        }
        public static CheckStatusOk createOk(SaveStatus status, Ballot promised, Ballot accepted, @Nullable Timestamp executeAt,
                                             boolean isCoordinating, Durability durability,
                                             @Nullable AbstractRoute route, @Nullable RoutingKey homeKey,
                                             PartialTxn partialTxn, PartialDeps committedDeps, Writes writes, Result result)
        {
            return new CheckStatusOkFull(status, promised, accepted, executeAt, isCoordinating, durability, route, homeKey,
                                         partialTxn, committedDeps, writes, result);
        }
    }

    // order is important
    public enum IncludeInfo
    {
        No, Route, All
    }

    public final RoutingKeys someKeys;
    public final long startEpoch;
    public final long endEpoch;
    public final IncludeInfo includeInfo;

    public CheckStatus(TxnId txnId, RoutingKeys someKeys, long startEpoch, long endEpoch, IncludeInfo includeInfo)
    {
        super(txnId);
        this.someKeys = someKeys;
        this.startEpoch = startEpoch;
        this.endEpoch = endEpoch;
        this.includeInfo = includeInfo;
    }

    @Override
    public Iterable<TxnId> txnIds()
    {
        return Collections.singleton(txnId);
    }

    @Override
    public Iterable<Key> keys()
    {
        return Collections.emptyList();
    }

    public CheckStatus(Id to, Topologies topologies, TxnId txnId, RoutingKeys someKeys, IncludeInfo includeInfo)
    {
        super(txnId);
        // TODO (now): cleanup use of instanceof to avoid hotspot cache thrashing
        if (someKeys instanceof AbstractRoute)
            this.someKeys = computeScope(to, topologies, (AbstractRoute) someKeys, 0, AbstractRoute::sliceStrict, PartialRoute::union);
        else
            this.someKeys = computeScope(to, topologies, someKeys, 0, RoutingKeys::slice, RoutingKeys::union);
        this.startEpoch = topologies.oldestEpoch();
        this.endEpoch = topologies.currentEpoch();
        this.includeInfo = includeInfo;
    }

    public void process()
    {
        node.mapReduceConsumeLocal(this, someKeys, startEpoch, endEpoch, this);
    }

    @Override
    public CheckStatusOk apply(SafeCommandStore instance)
    {
        Command command = instance.command(txnId);
        switch (includeInfo)
        {
            default: throw new IllegalStateException();
            case No:
            case Route:
                return new CheckStatusOk(command.saveStatus(), command.promised(), command.accepted(), command.executeAt(),
                        node.isCoordinating(txnId, command.promised()),
                        command.durability(), includeInfo == IncludeInfo.No ? null : command.route(), command.homeKey());
            case All:
                return new CheckStatusOkFull(node, command);
        }    }

    @Override
    public CheckStatusOk reduce(CheckStatusOk r1, CheckStatusOk r2)
    {
        return r1.merge(r2);
    }

    @Override
    public void accept(CheckStatusOk ok, Throwable failure)
    {
        if (ok == null) node.reply(replyTo, replyContext, CheckStatusNack.nack());
        else node.reply(replyTo, replyContext, ok);
    }

    public interface CheckStatusReply extends Reply
    {
        boolean isOk();
    }

    public static class CheckStatusOk implements CheckStatusReply
    {
        public final SaveStatus saveStatus;
        public final Ballot promised;
        public final Ballot accepted;
        public final @Nullable Timestamp executeAt; // not set if invalidating or invalidated
        public final boolean isCoordinating;
        public final Durability durability; // i.e. on all shards
        public final @Nullable AbstractRoute route;
        public final @Nullable RoutingKey homeKey;

        public CheckStatusOk(Node node, Command command)
        {
            this(command.saveStatus(), command.promised(), command.accepted(), command.executeAt(),
                 node.isCoordinating(command.txnId(), command.promised()), command.durability(), command.route(), command.homeKey());
        }

        private CheckStatusOk(SaveStatus saveStatus, Ballot promised, Ballot accepted, @Nullable Timestamp executeAt,
                              boolean isCoordinating, Durability durability,
                              @Nullable AbstractRoute route, @Nullable RoutingKey homeKey)
        {
            this.saveStatus = saveStatus;
            this.promised = promised;
            this.accepted = accepted;
            this.executeAt = executeAt;
            this.isCoordinating = isCoordinating;
            this.durability = durability;
            this.route = route;
            this.homeKey = homeKey;
        }

        public ProgressToken toProgressToken()
        {
            return new ProgressToken(durability, saveStatus.status, promised, accepted);
        }

        @Override
        public boolean isOk()
        {
            return true;
        }

        @Override
        public String toString()
        {
            return "CheckStatusOk{" +
                   "status:" + saveStatus +
                   ", promised:" + promised +
                   ", accepted:" + accepted +
                   ", executeAt:" + executeAt +
                   ", durability:" + durability +
                   ", isCoordinating:" + isCoordinating +
                   ", route:" + route +
                   ", homeKey:" + homeKey +
                   '}';
        }

        public CheckStatusOk merge(CheckStatusOk that)
        {
            if (that.saveStatus.compareTo(this.saveStatus) > 0)
                return that.merge(this);

            // preferentially select the one that is coordinating, if any
            CheckStatusOk prefer = this.isCoordinating ? this : that;
            CheckStatusOk defer = prefer == this ? that : this;

            // then select the max along each criteria, preferring the coordinator
            CheckStatusOk maxAccepted = prefer.accepted.compareTo(defer.accepted) >= 0 ? prefer : defer;
            CheckStatusOk maxStatus; {
                int c = prefer.saveStatus.compareTo(defer.saveStatus);
                if (c > 0) maxStatus = prefer;
                else if (c < 0) maxStatus = defer;
                else maxStatus = maxAccepted;
            }
            CheckStatusOk maxPromised = prefer.promised.compareTo(defer.promised) >= 0 ? prefer : defer;
            CheckStatusOk maxDurability = prefer.durability.compareTo(defer.durability) >= 0 ? prefer : defer;
            CheckStatusOk maxHomeKey = prefer.homeKey != null || defer.homeKey == null ? prefer : defer;
            AbstractRoute mergedRoute = AbstractRoute.merge(prefer.route, defer.route);

            // if the maximum (or preferred equal) is the same on all dimensions, return it
            if (maxStatus == maxPromised && maxStatus == maxAccepted && maxStatus == maxDurability
                && maxStatus.route == mergedRoute && maxStatus == maxHomeKey)
            {
                return maxStatus;
            }

            // otherwise assemble the maximum of each, and propagate isCoordinating from the origin we selected the promise from
            boolean isCoordinating = maxPromised == prefer ? prefer.isCoordinating : defer.isCoordinating;
            return new CheckStatusOk(maxStatus.saveStatus, maxPromised.promised, maxAccepted.accepted, maxStatus.executeAt,
                                     isCoordinating, maxDurability.durability, mergedRoute, maxHomeKey.homeKey);
        }

        @Override
        public MessageType type()
        {
            return MessageType.CHECK_STATUS_RSP;
        }
    }

    public static class CheckStatusOkFull extends CheckStatusOk
    {
        public static final CheckStatusOkFull NOT_WITNESSED = new CheckStatusOkFull(NotWitnessed, Ballot.ZERO, Ballot.ZERO, Timestamp.NONE, false, NotDurable, null, null, null, null, null, null);

        public final PartialTxn partialTxn;
        public final PartialDeps committedDeps; // only set if status >= Committed, so safe to merge
        public final Writes writes;
        public final Result result;

        public CheckStatusOkFull(Node node, Command command)
        {
            super(node, command);
            this.partialTxn = command.partialTxn();
            this.committedDeps = command.status().compareTo(Committed) >= 0 ? command.partialDeps() : null;
            this.writes = command.writes();
            this.result = command.result();
        }

        protected CheckStatusOkFull(SaveStatus status, Ballot promised, Ballot accepted, Timestamp executeAt,
                                  boolean isCoordinating, Durability durability, AbstractRoute route,
                                  RoutingKey homeKey, PartialTxn partialTxn, PartialDeps committedDeps, Writes writes, Result result)
        {
            super(status, promised, accepted, executeAt, isCoordinating, durability, route, homeKey);
            this.partialTxn = partialTxn;
            this.committedDeps = committedDeps;
            this.writes = writes;
            this.result = result;
        }

        /**
         * This method assumes parameter is of the same type and has the same additional info (modulo partial replication).
         * If parameters have different info, it is undefined which properties will be returned.
         *
         * This method is NOT guaranteed to return CheckStatusOkFull unless the parameter is also CheckStatusOkFull.
         * This method is NOT guaranteed to return either parameter: it may merge the two to represent the maximum
         * combined info, (and in this case if the parameter were not CheckStatusOkFull, and were the higher status
         * reply, the info would potentially be unsafe to act upon when given a higher status
         * (e.g. Accepted executeAt is very different to Committed executeAt))
         */
        public CheckStatusOk merge(CheckStatusOk that)
        {
            CheckStatusOk max = super.merge(that);
            CheckStatusOk maxSrc = this.saveStatus.compareTo(that.saveStatus) >= 0 ? this : that;
            if (!(maxSrc instanceof CheckStatusOkFull))
                return max;

            CheckStatusOkFull fullMax = (CheckStatusOkFull) maxSrc;
            CheckStatusOk minSrc = maxSrc == this ? that : this;
            if (!(minSrc instanceof CheckStatusOkFull))
            {
                return new CheckStatusOkFull(max.saveStatus, max.promised, max.accepted, fullMax.executeAt, max.isCoordinating, max.durability, max.route,
                                             max.homeKey, fullMax.partialTxn, fullMax.committedDeps, fullMax.writes, fullMax.result);
            }

            CheckStatusOkFull fullMin = (CheckStatusOkFull) minSrc;

            PartialTxn partialTxn = PartialTxn.merge(fullMax.partialTxn, fullMin.partialTxn);
            PartialDeps committedDeps;
            if (fullMax.committedDeps == null) committedDeps = fullMin.committedDeps;
            else if (fullMin.committedDeps == null) committedDeps = fullMax.committedDeps;
            else committedDeps = fullMax.committedDeps.with(fullMin.committedDeps);

            return new CheckStatusOkFull(max.saveStatus, max.promised, max.accepted, fullMax.executeAt, max.isCoordinating, max.durability, max.route,
                                         max.homeKey, partialTxn, committedDeps, fullMax.writes, fullMax.result);
        }

        public Known sufficientFor(AbstractKeys<?, ?> forKeys)
        {
            return sufficientFor(forKeys, saveStatus, partialTxn, committedDeps, writes, result);
        }

        private static Known sufficientFor(AbstractKeys<?, ?> forKeys, SaveStatus maxStatus, PartialTxn partialTxn, PartialDeps committedDeps, Writes writes, Result result)
        {
            Known learn = maxStatus.known;
            switch (maxStatus.known)
            {
                default: throw new AssertionError();
                case Invalidation:
                    break;
                case Outcome:
                    if (writes != null && result != null
                        && committedDeps != null && committedDeps.covers(forKeys)
                        && partialTxn != null && partialTxn.covers(forKeys))
                        break;
                    learn = Known.ExecutionOrder;
                case ExecutionOrder:
                    if (committedDeps != null && committedDeps.covers(forKeys)
                        && partialTxn != null && partialTxn.covers(forKeys))
                        break;
                    learn = Known.Definition;
                case Definition:
                    if (partialTxn != null && partialTxn.covers(forKeys))
                        break;
                    learn = Known.Nothing;
                    // TODO (now): we should test Route presence here
                case Nothing:
            }
            return learn;
        }

        @Override
        public String toString()
        {
            return "CheckStatusOk{" +
                   "status:" + saveStatus +
                   ", promised:" + promised +
                   ", accepted:" + accepted +
                   ", executeAt:" + executeAt +
                   ", durability:" + durability +
                   ", isCoordinating:" + isCoordinating +
                   ", deps:" + committedDeps +
                   ", writes:" + writes +
                   ", result:" + result +
                   '}';
        }
    }

    public static class CheckStatusNack implements CheckStatusReply
    {
        private static final CheckStatusNack instance = new CheckStatusNack();

        private CheckStatusNack() { }

        @Override
        public MessageType type()
        {
            return MessageType.CHECK_STATUS_RSP;
        }

        public static CheckStatusNack nack()
        {
            return instance;
        }

        @Override
        public boolean isOk()
        {
            return false;
        }

        @Override
        public String toString()
        {
            return "CheckStatusNack";
        }
    }

    @Override
    public String toString()
    {
        return "CheckStatus{" +
               "txnId:" + txnId +
               '}';
    }

    @Override
    public MessageType type()
    {
        return MessageType.CHECK_STATUS_REQ;
    }

    @Override
    public long waitForEpoch()
    {
        return endEpoch;
    }
}