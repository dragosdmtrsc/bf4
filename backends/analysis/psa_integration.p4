
extern bool platform_port_valid(in PortId_t p);
extern Timestamp_t now();

extern bool is_cpu_port(in PortId_t p);
@controlled()
extern bool constrain(@readonly() mutable_packet pin);

@impl("INGRESS_apply_")
extern void INGRESS_apply(mutable_packet p,
        inout psa_ingress_output_metadata_t ostd,
        inout psa_ingress_parser_input_metadata_t istd,
        inout {{ RESUB }} resub,
        inout {{ RECIRC }} recirc,
        inout {{ CI2E }} clone_i2e_meta,
        inout {{ NM }} normal_meta);

@impl("EGRESS_apply_")
extern void EGRESS_apply(mutable_packet p,
                        inout psa_egress_parser_input_metadata_t istd,
                        inout psa_egress_input_metadata_t instd,
                        inout psa_egress_output_metadata_t ostd,
                        inout psa_egress_deparser_input_metadata_t edim,
                        inout {{ RESUB }} resub,
                        inout {{ RECIRC }} recirc,
                        inout {{ CI2E }} clone_i2e_meta,
                        inout {{ CE2E }} clone_e2e_meta,
                        inout {{ NM }} normal_meta);

@impl("PSAImpl_egress_start_") @noreturn()
extern void PSAImpl_egress_start(mutable_packet p,
           inout psa_egress_parser_input_metadata_t istd,
           inout psa_egress_input_metadata_t instd,
           inout psa_egress_deparser_input_metadata_t edim,
           inout {{ RESUB }} resub,
           inout {{ RECIRC }} recirc,
           inout {{ CI2E }} clone_i2e_meta,
           inout {{ CE2E }} clone_e2e_meta,
           inout {{ NM }} normal_meta
           );
@impl("PSAImpl_ingress_start_") @noreturn()
extern void PSAImpl_ingress_start(mutable_packet p,
                              inout psa_ingress_parser_input_metadata_t istd,
                              inout {{ RESUB }} resub,
                              inout {{ RECIRC }} recirc,
                              inout {{ CE2E }} clone_e2e_meta);

void INGRESS_apply_(mutable_packet p,
        inout psa_ingress_output_metadata_t ostd,
        inout psa_ingress_parser_input_metadata_t istd,
        inout {{ RESUB }} resub,
        inout {{ RECIRC }} recirc,
        inout {{ CI2E }} clone_i2e_meta,
        inout {{ NM }} normal_meta) {
    {{ IH }} headers__;
    {{ IM }} meta_;
    {{ declare("ip") }};
    {{ declare("id") }};
    {{ declare("ig") }};
    psa_ingress_input_metadata_t instd;
    instd.ingress_timestamp = now();
    error last = error.NoError;
    ip.apply(p, headers__, meta_, istd, resub, recirc, last);
    instd.ingress_port = istd.ingress_port;
    instd.packet_path = istd.packet_path;
    instd.parser_error = last;
    ostd.class_of_service = do_cast(0, ostd.class_of_service);
    ostd.clone = false;
    ostd.drop = true;
    ostd.resubmit = false;
    ostd.multicast_group = do_cast(0, ostd.multicast_group);
    ig.apply(headers__, meta_, instd, ostd);
    mutable_packet(4096) p0;
    emptyPacket(p0);
    id.apply(p0, clone_i2e_meta, resub, normal_meta, headers__,
             meta_, ostd);
    prependPacket(p, p0);
}

void EGRESS_apply_(mutable_packet p,
                 inout psa_egress_parser_input_metadata_t istd,
                 inout psa_egress_input_metadata_t instd,
                 inout psa_egress_output_metadata_t ostd,
                 inout psa_egress_deparser_input_metadata_t edim,
                 inout {{ RESUB }} resub,
                 inout {{ RECIRC }} recirc,
                 inout {{ CI2E }} clone_i2e_meta,
                 inout {{ CE2E }} clone_e2e_meta,
                 inout {{ NM }} normal_meta)
  {
    {{ EH }} headers_;
    {{ EM }} meta_;
    {{ declare("ep") }};
    {{ declare("eg") }};
    {{ declare("ed") }};
    instd.egress_timestamp = now();
    instd.egress_port = istd.egress_port;
    error last;
    ep.apply(p, headers_, meta_, istd, normal_meta, clone_i2e_meta, clone_e2e_meta, last);
    instd.parser_error = last;
    ostd.clone = false;
    ostd.drop = true;
    instd.packet_path = istd.packet_path;
    eg.apply(headers_, meta_, instd, ostd);
    edim.egress_port = istd.egress_port;
    mutable_packet(4096) p0;
    emptyPacket(p0);
    ed.apply(p0, clone_e2e_meta, recirc, headers_, meta_, ostd, edim);
    prependPacket(p, p0);
}

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

@controlled()
extern clone_session_t qquery_first_clone_pre(in CloneSessionId_t cs);
@controlled()
extern clone_session_t qquery_all_clone_pre(in CloneSessionId_t cs);
@controlled()
extern clone_session_t qquery_first_mcast(in MulticastGroup_t cs);
@controlled()
extern clone_session_properties_t qquery_clone_session_properties(in CloneSessionId_t cs);


void PSAImpl_egress_start_(mutable_packet p,
    inout psa_egress_parser_input_metadata_t istd,
    inout psa_egress_input_metadata_t instd,
    inout psa_egress_deparser_input_metadata_t edim,
    inout {{ RESUB }} resub,
    inout {{ RECIRC }} recirc,
    inout {{ CI2E }} clone_i2e_meta,
    inout {{ CE2E }} clone_e2e_meta,
    inout {{ NM }} normal_meta
    )
  {
    psa_egress_output_metadata_t ostd;
    mutable_packet(4096) old;
    copyPacket(old, p);
    copyPacket(old, p);
    EGRESS_apply(p,
                 istd, instd, ostd, edim, resub, recirc, clone_i2e_meta,
                 clone_e2e_meta, normal_meta);
    if (ostd.clone && havoc<bool>()) {
      clone_session_t cls =
          qquery_first_clone_pre(ostd.clone_session_id);
      clone_session_properties_t cs =
          qquery_clone_session_properties(ostd.clone_session_id);
      istd.egress_port = cls.port;
      istd.packet_path = PSA_PacketPath_t.CLONE_E2E;
      instd.instance = cls.instance;
      instd.egress_port = cls.port;
      PSAImpl_egress_start(p, istd, instd, edim, resub, recirc, clone_i2e_meta,
                           clone_e2e_meta, normal_meta);
    }
    if (psa_recirculate(ostd, edim)) {
        // do recirculate logic
        do_drop();
    }
    if (platform_port_valid(instd.egress_port)) {
        do_send(instd.egress_port, p);
    }
    do_drop();
  }

void PSAImpl_ingress_start_(mutable_packet p,
                              inout psa_ingress_parser_input_metadata_t istd,
                              inout {{ RESUB }} resub,
                              inout {{ RECIRC }} recirc,
                              inout {{ CE2E }} clone_e2e_meta)
  {
    psa_ingress_output_metadata_t ostd;
    {{ CI2E }} clone_i2e_meta;
    {{ NM }} normal_meta;
    mutable_packet(4096) old;
    copyPacket(old, p);
    INGRESS_apply(p,
                  ostd,
                  istd,
                  resub,
                  recirc,
                  clone_i2e_meta,
                  normal_meta);
    if (ostd.clone && havoc<bool>()) {
      angelic_assert(true);
      clone_session_t cls =
          qquery_first_clone_pre(ostd.clone_session_id);
      angelic_assert(true);
      clone_session_properties_t cs =
          qquery_clone_session_properties(ostd.clone_session_id);
      psa_egress_parser_input_metadata_t einstd;
      einstd.egress_port = cls.port;
      einstd.packet_path = PSA_PacketPath_t.CLONE_I2E;
      psa_egress_input_metadata_t eostd;
      eostd.instance = cls.instance;
      eostd.egress_port = cls.port;
      psa_egress_deparser_input_metadata_t edim;
      PSAImpl_egress_start(old, einstd, eostd, edim, resub, recirc,
                           clone_i2e_meta, clone_e2e_meta, normal_meta);
    }
    if (ostd.drop) {
      do_drop();
    }
    if (ostd.resubmit) {
      istd.packet_path = PSA_PacketPath_t.RESUBMIT;
      copyPacket(p, old);
      PSAImpl_ingress_start(p, istd, resub, recirc, clone_e2e_meta);
      return;
    }
    if (ostd.multicast_group != do_cast(0, ostd.multicast_group)) {
      clone_session_t cs = qquery_first_mcast(ostd.multicast_group);
      angelic_assert(true);
      psa_egress_parser_input_metadata_t einstd;
      einstd.egress_port = cs.port;
      einstd.packet_path = PSA_PacketPath_t.NORMAL_MULTICAST;
      psa_egress_input_metadata_t eostd;
      eostd.instance = cs.instance;
      eostd.egress_port = cs.port;
      psa_egress_deparser_input_metadata_t edim;
      PSAImpl_egress_start(p, einstd, eostd, edim, resub, recirc,
                           clone_i2e_meta, clone_e2e_meta, normal_meta);

      return;
    }
    if (ostd.egress_port == (PortId_t)0) {
        bug();
    }
    if (platform_port_valid(ostd.egress_port)) {
      psa_egress_parser_input_metadata_t einstd;
      einstd.egress_port = ostd.egress_port;
      einstd.packet_path = PSA_PacketPath_t.NORMAL_UNICAST;
      psa_egress_input_metadata_t eostd;
      eostd.instance = do_cast(0, eostd.instance);
      eostd.egress_port = ostd.egress_port;
      psa_egress_deparser_input_metadata_t edim;
      PSAImpl_egress_start(p, einstd, eostd, edim, resub, recirc,
                           clone_i2e_meta, clone_e2e_meta, normal_meta);
    } else {
      do_drop();
    }
  }

void run() {
    mutable_packet(4096) pin;
    readPacket(pin);
    PortId_t p = havoc<PortId_t>();
    if (!platform_port_valid(p)  || p == PSA_PORT_RECIRCULATE) {
        do_drop();
    }
    if (is_cpu_port(p)) {
        if (!constrain(pin)) {
            do_drop();
        }
    } else {
        angelic_assert(true);
    }
    {{ RESUB }} resub;
    {{ RECIRC }} recirc;
    {{ CE2E }} ce2em;
    psa_ingress_parser_input_metadata_t istd;
    istd.ingress_port = p;
    istd.packet_path = PSA_PacketPath_t.NORMAL;
    PSAImpl_ingress_start(pin, istd, resub, recirc, ce2em);
}
