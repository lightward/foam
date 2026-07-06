-- Counter: the platform schema. Distinct from ../schema.sql in every respect —
-- this is the app's database, not the charge-ledger instrument. Four tables,
-- pedestrian on purpose: tables are the constructor data of the kit's carrier
-- types and nothing else (sim/Sim/Model.lean); readings are views; export is
-- projection (sim/Sim/Json.lean, model_roundtrip — the codec carries a receipt).
--
-- What the Lean cannot state cannot be stored. An act has a signer and content,
-- never an object-actor: the accusative gets no column (counter/Counter/
-- Declension.lean — the profane sentence cannot be persisted; safety is absent
-- terrain, not a validation rule).
--
-- No journaling. The user's act-list is a model under composition, not a ledger:
-- rows are reorderable, editable, deletable (Hanoi play toward recursive health
-- is guided defect-descent, counter/Counter/Health.lean). Integrity is carried
-- by grammar + receipts (the export self-verifies on arrival), and the one
-- append-only order-reading in the system lives downstage in the WAL, which is
-- checkpointed and truncated: held + tail, the licensed forgetting
-- (Foam/Engine/Summary.lean summary_resumes).

create table users (
  id         bigint generated always as identity primary key,
  email      text not null unique,
  created_at timestamptz not null default now()
);

create table actors (
  id         bigint generated always as identity primary key,
  user_id    bigint not null references users (id),
  parent_id  bigint references actors (id),
  name       text not null,
  created_at timestamptz not null default now(),
  updated_at timestamptz not null default now(),
  unique (user_id, id)
);

create table acts (
  id         bigint generated always as identity primary key,
  user_id    bigint not null references users (id),
  actor_id   bigint not null references actors (id),
  position   integer not null,
  verb       text not null,
  src        text not null,
  dst        text not null,
  created_at timestamptz not null default now(),
  updated_at timestamptz not null default now()
);

create index acts_by_model on acts (user_id, position);
create index acts_by_actor on acts (actor_id, position);

-- Harvests are the exception: a readout happened, priced and signed. The walk
-- that produced it is already released (exploration writes nothing; the harvest
-- is exactly the gauge-invariant content). Rows here are not edited.
create table readouts (
  id         bigint generated always as identity primary key,
  user_id    bigint not null references users (id),
  params     jsonb not null,
  harvest    jsonb not null,
  created_at timestamptz not null default now()
);

-- The reading tower, as views. SQL's own operators are the posts:
-- WHERE is the membrane filter, ORDER BY is the order-reading, GROUP BY/COUNT
-- is freq (money's reading), the fold to position is netAct. One carrier,
-- many posts (counter/Counter/Packing.lean one_carrier_many_posts).

create view composed as        -- the model as declared: composition order
select * from acts order by user_id, position;

create view own_frames as      -- the genitive: each actor's own stream
select actor_id, user_id, position, verb, src, dst
from acts order by actor_id, position;

create view quiver as          -- the act-map: edges are a reading of acts
select distinct user_id, src, dst from acts;

create view windings as        -- freq: permutation-blind, money's reading
select user_id, actor_id, verb, count(*) as winding
from acts group by user_id, actor_id, verb;

create view handles as         -- the node set, derived
select user_id, src as handle from acts
union
select user_id, dst from acts;
