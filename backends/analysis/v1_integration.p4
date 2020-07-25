
typedef bit<9> PortId_t;
typedef bit<48> Timestamp_t;
typedef bit<16> CloneSessionId_t;
typedef bit<16> MulticastGroup_t;
typedef bit<16> EgressInstance_t;
typedef bit<3> ClassOfService_t;
typedef bit<32> PacketLength_t;
typedef bit<32> InstanceType_t;

const InstanceType_t PKT_INSTANCE_TYPE_NORMAL = 32w0;
const InstanceType_t PKT_INSTANCE_TYPE_INGRESS_CLONE = 32w1;
const InstanceType_t PKT_INSTANCE_TYPE_EGRESS_CLONE = 32w2;
const InstanceType_t PKT_INSTANCE_TYPE_RESUBMIT = 32w3;
const InstanceType_t PKT_INSTANCE_TYPE_REPLICATION = 32w4;
const InstanceType_t PKT_INSTANCE_TYPE_RECIRC = 32w5;

extern bool platform_port_valid(in PortId_t p);
extern Timestamp_t now();

extern bool is_cpu_port(in PortId_t p);
@controlled()
extern bool constrain(@readonly() mutable_packet pin);

@impl("parse_and_run_") @noreturn()
extern void parse_and_run(mutable_packet pin,
    inout {{ M }} metas_,
    inout standard_metadata_t standard_meta);

@impl("PSAImpl_egress_start_") @noreturn()
extern void PSAImpl_egress_start(mutable_packet p,
                     inout {{ H }} hdrs_,
                     inout {{ M }} metas_,
                     inout standard_metadata_t standard_meta);

@impl("PSAImpl_ingress_start_") @noreturn()
extern void PSAImpl_ingress_start(mutable_packet p,
                    inout {{ H }} hdrs_,
                    inout {{ M }} metas_,
                    inout standard_metadata_t standard_meta);

extern void zero_out<T>(inout T x);

struct clone_session_t {
  bool exists;
  PortId_t port;
  EgressInstance_t instance;
}
struct clone_session_properties_t {
  bool exists;
  ClassOfService_t class_of_service;
  bool trunc;
  PacketLength_t plen;
}

@controlled() extern clone_session_t
    qquery_first_clone_pre(in CloneSessionId_t cs);
@controlled() extern clone_session_t
    qquery_all_clone_pre(in CloneSessionId_t cs);
@controlled() extern clone_session_t qquery_first_mcast(in MulticastGroup_t cs);
@controlled() extern clone_session_properties_t
    qquery_clone_session_properties(in CloneSessionId_t cs);

void PSAImpl_egress_start_(mutable_packet p,
                           inout {{ H }} hdrs_,
                           inout {{ M }} metas_,
                           inout standard_metadata_t standard_meta) {
  {{ declare("eg") }};
  {{ declare("dep") }};
  {{ H }} clone_hdrs;
  {{ M }} clone_metas;
  standard_metadata_t clone_sm;
  clone_sm = standard_meta;
  clone_hdrs = hdrs_;
  clone_metas = metas_;
  eg.apply(hdrs_, metas_, standard_meta);
  CloneSessionId_t clone_session = standard_meta.clone_spec[15:0];
  CloneSessionId_t clone_field_list = standard_meta.clone_spec[31:16];
  if (clone_session != 0) {
      clone_session_t cs = qquery_first_clone_pre(clone_session);
      copy_field_list(metas_, clone_metas, standard_meta, clone_sm,
                            (bit<16>)clone_field_list);
      clone_sm.instance_type = PKT_INSTANCE_TYPE_EGRESS_CLONE;
      clone_sm.egress_port = cs.port;
      clone_sm.resubmit_flag = 0;
      clone_sm.clone_spec = 0;
      if (havoc<bool>()) {
          // egress clone
          PSAImpl_egress_start(p, clone_hdrs, clone_metas, clone_sm);
      }
  }
  if (standard_meta.egress_spec == 511) {
    do_drop();
  }
  dep.apply(p, hdrs_);
  bit<32> recirculate_flag = standard_meta.recirculate_flag;
  if (recirculate_flag != 0) {
      zero_out(clone_metas);
      copy_field_list(metas_, clone_metas, standard_meta, clone_sm,
                            (bit<16>)recirculate_flag);
      clone_sm.resubmit_flag = 0;
      clone_sm.clone_spec = 0;
      clone_sm.recirculate_flag = 0;
      clone_sm.egress_spec = 0;
      clone_sm.egress_port = 0;
      clone_sm.instance_type = PKT_INSTANCE_TYPE_RECIRC;
      copy_field_list(metas_, clone_metas, standard_meta, clone_sm,
                            (bit<16>)recirculate_flag);
      parse_and_run(p, clone_metas, clone_sm);
  }
  do_send(standard_meta.egress_port, p);
}

void PSAImpl_ingress_start_(mutable_packet p,
        inout {{ H }} hdrs_,
        inout {{ M }} metas_,
        inout standard_metadata_t standard_meta) {
    {{ declare("ig") }};
    {{ H }} clone_hdrs;
    {{ M }} clone_metas;
    standard_metadata_t clone_sm;
    clone_sm = standard_meta;
    clone_hdrs = hdrs_;
    clone_metas = metas_;
    ig.apply(hdrs_, metas_, standard_meta);
    CloneSessionId_t clone_session = standard_meta.clone_spec[15:0];
    CloneSessionId_t clone_field_list = standard_meta.clone_spec[31:16];
    MulticastGroup_t mgid = standard_meta.mcast_grp;
    bit<32> resubmit_flag = standard_meta.resubmit_flag;
    if (clone_session != 0) {
        clone_session_t cs = qquery_first_clone_pre(clone_session);
        copy_field_list(metas_, clone_metas,
                    standard_meta, clone_sm,
                    (bit<16>)clone_field_list);
        clone_sm.egress_port = cs.port;
        clone_sm.resubmit_flag = 0;
        clone_sm.clone_spec = 0;
        clone_sm.recirculate_flag = 0;
        clone_sm.egress_spec = 0;
        clone_sm.egress_port = 0;
        clone_sm.instance_type = PKT_INSTANCE_TYPE_INGRESS_CLONE;
        if (havoc<bool>()) {
            // egress
            PSAImpl_egress_start(p, clone_hdrs, clone_metas, clone_sm);
        }
        standard_meta.resubmit_flag = 0;
        standard_meta.clone_spec = 0;
        standard_meta.recirculate_flag = 0;
    }
    if (resubmit_flag != 0) {
      copy_field_list(metas_, clone_metas, standard_meta, clone_sm,
                          (bit<16>)resubmit_flag);
      clone_sm = standard_meta;
      clone_sm.resubmit_flag = 0;
      clone_sm.clone_spec = 0;
      clone_sm.recirculate_flag = 0;
      clone_sm.egress_spec = 0;
      clone_sm.egress_port = 0;
      clone_sm.instance_type = PKT_INSTANCE_TYPE_RESUBMIT;
      PSAImpl_ingress_start(p, clone_hdrs, clone_metas, clone_sm);
    }
    if (mgid != 0) {
        standard_meta.instance_type = PKT_INSTANCE_TYPE_REPLICATION;
        clone_session_t ms = qquery_first_mcast(mgid);
        standard_meta.egress_port = ms.port;
        standard_meta.egress_rid = ms.instance;
        PSAImpl_egress_start(p, hdrs_, metas_, standard_meta);
    }
    if (standard_meta.egress_spec == 511) {
        do_drop();
    }
    standard_meta.egress_port = standard_meta.egress_spec;
    standard_meta.instance_type = PKT_INSTANCE_TYPE_NORMAL;
    PSAImpl_egress_start(p, hdrs_, metas_, standard_meta);
}

void parse_and_run_(mutable_packet pin,
    inout {{ M }} metas_,
    inout standard_metadata_t standard_meta) {
  error last;
  standard_meta.ingress_global_timestamp = now();
  {{ H }} hdrs_;
  zero_out(hdrs_);
  {{ declare("p") }};
  last = error.NoError;
  p.apply(pin, hdrs_, metas_, standard_meta, last);
  standard_meta.parser_error = last;
  PSAImpl_ingress_start(pin, hdrs_, metas_, standard_meta);
}

void run() {
  mutable_packet(4096) pin;
  readPacket(pin);
  PortId_t p = havoc<PortId_t>();
  standard_metadata_t standard_meta;
  if (!platform_port_valid(p)) {
    do_drop();
  }
  if (is_cpu_port(p)) {
    if (!constrain(pin)) {
      do_drop();
    }
  } else {
    angelic_assert(true);
  }
  zero_out(standard_meta);
  standard_meta.ingress_port = p;
  error last;
  standard_meta.ingress_global_timestamp = now();
  {{ M }} metas_;
  zero_out(metas_);
  standard_meta.instance_type = PKT_INSTANCE_TYPE_NORMAL;
  parse_and_run(pin, metas_, standard_meta);
}
