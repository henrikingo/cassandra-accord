package accord.messages;

import accord.local.Node;
import accord.local.Node.Id;
import accord.topology.Topologies;
import accord.txn.Timestamp;
import accord.txn.Dependencies;
import accord.txn.Txn;
import accord.txn.TxnId;

// TODO: CommitOk responses, so we can send again if no reply received? Or leave to recovery?
public class Commit extends ReadData
{
    final Dependencies deps;
    final boolean read;

    public Commit(Scope scope, TxnId txnId, Txn txn, Timestamp executeAt, Dependencies deps, boolean read)
    {
        super(scope, txnId, txn, executeAt);
        this.deps = deps;
        this.read = read;
    }

    public Commit(Id to, Topologies topologies, TxnId txnId, Txn txn, Timestamp executeAt, Dependencies deps, boolean read)
    {
        this(Scope.forTopologies(to, topologies, txn), txnId, txn, executeAt, deps, read);
    }

    public void process(Node node, Id from, long messageId)
    {
        node.local(scope()).forEach(instance -> instance.command(txnId).commit(txn, deps, executeAt));
        if (read) super.process(node, from, messageId);
    }

    @Override
    public String toString()
    {
        return "Commit{txnId: " + txnId +
               ", executeAt: " + executeAt +
               ", deps: " + deps +
               ", read: " + read +
               '}';
    }
}