#define _POSIX_C_SOURCE 200809L
/*
 * test2.c: Linux console app to test receiving all CAN frames - std and
 *          ext ID frames - with Taxtrix OpenPort 2.0 logger on USB port.
 *
 */
#include "j2534.h"

#include <ctype.h>
#include <errno.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MIN_READ_TIMEOUT_MS 1UL
#define DEFAULT_BITRATE 500000UL
#define READ_TIMEOUT_MS 200UL

/* Protocol IDs are not defined in this j2534.h, so keep them local. */
#define J2534_PROTO_J1850VPW     1UL
#define J2534_PROTO_J1850PWM     2UL
#define J2534_PROTO_ISO9141      3UL
#define J2534_PROTO_ISO14230     4UL
#define J2534_PROTO_CAN          5UL
#define J2534_PROTO_ISO15765     6UL
#define J2534_PROTO_SCI_A_ENGINE 7UL
#define J2534_PROTO_SCI_A_TRANS  8UL
#define J2534_PROTO_SCI_B_ENGINE 9UL
#define J2534_PROTO_SCI_B_TRANS  10UL

#define J2534_LOOPBACK 0x03UL
#define J2534_OFF      0x00UL
#define J2534_ON       0x01UL

/* Common J2534 CAN connect flags (not defined in this j2534.h). */
#define J2534_CAN_29BIT_ID 0x00000100UL
#define J2534_CAN_ID_BOTH  0x00000800UL

static volatile sig_atomic_t g_stop = 0;

static void on_sigint(int sig)
{
  (void)sig;
  g_stop = 1;
}

static const char *j2534_err_str(int32_t status)
{
  switch ((enum j2534_error)status) {
    case J2534_NOERROR:
      return "J2534_NOERROR";
    case J2534_ERR_NOT_SUPPORTED:
      return "J2534_ERR_NOT_SUPPORTED";
    case J2534_ERR_INVALID_CHANNEL_ID:
      return "J2534_ERR_INVALID_CHANNEL_ID";
    case J2534_ERR_INVALID_PROTOCOL_ID:
      return "J2534_ERR_INVALID_PROTOCOL_ID";
    case J2534_ERR_NULL_PARAMETER:
      return "J2534_ERR_NULL_PARAMETER";
    case J2534_ERR_INVALID_IOCTL_VALUE:
      return "J2534_ERR_INVALID_IOCTL_VALUE";
    case J2534_ERR_INVALID_FLAGS:
      return "J2534_ERR_INVALID_FLAGS";
    case J2534_ERR_FAILED:
      return "J2534_ERR_FAILED";
    case J2534_ERR_DEVICE_NOT_CONNECTED:
      return "J2534_ERR_DEVICE_NOT_CONNECTED";
    case J2534_ERR_TIMEOUT:
      return "J2534_ERR_TIMEOUT";
    case J2534_ERR_INVALID_MSG:
      return "J2534_ERR_INVALID_MSG";
    case J2534_ERR_INVALID_TIME_INTERVAL:
      return "J2534_ERR_INVALID_TIME_INTERVAL";
    case J2534_ERR_EXCEEDED_LIMIT:
      return "J2534_ERR_EXCEEDED_LIMIT";
    case J2534_ERR_INVALID_MSG_ID:
      return "J2534_ERR_INVALID_MSG_ID";
    case J2534_ERR_DEVICE_IN_USE:
      return "J2534_ERR_DEVICE_IN_USE";
    case J2534_ERR_INVALID_IOCTL_ID:
      return "J2534_ERR_INVALID_IOCTL_ID";
    case J2534_ERR_BUFFER_EMPTY:
      return "J2534_ERR_BUFFER_EMPTY";
    case J2534_ERR_BUFFER_FULL:
      return "J2534_ERR_BUFFER_FULL";
    case J2534_ERR_BUFFER_OVERFLOW:
      return "J2534_ERR_BUFFER_OVERFLOW";
    case J2534_ERR_PIN_INVALID:
      return "J2534_ERR_PIN_INVALID";
    case J2534_ERR_CHANNEL_IN_USE:
      return "J2534_ERR_CHANNEL_IN_USE";
    case J2534_ERR_MSG_PROTOCOL_ID:
      return "J2534_ERR_MSG_PROTOCOL_ID";
    case J2534_ERR_INVALID_FILTER_ID:
      return "J2534_ERR_INVALID_FILTER_ID";
    case J2534_ERR_NO_FLOW_CONTROL:
      return "J2534_ERR_NO_FLOW_CONTROL";
    case J2534_ERR_NOT_UNIQUE:
      return "J2534_ERR_NOT_UNIQUE";
    case J2534_ERR_INVALID_BAUDRATE:
      return "J2534_ERR_INVALID_BAUDRATE";
    case J2534_ERR_INVALID_DEVICE_ID:
      return "J2534_ERR_INVALID_DEVICE_ID";
    default:
      return "J2534_ERR_UNKNOWN";
  }
}

static void print_last_error_if_any(void)
{
  char buf[256];
  memset(buf, 0, sizeof(buf));
  (void)PassThruGetLastError(buf);
  if (buf[0] != '\0') {
    printf("  LastError: %s\n", buf);
  }
}

static int hex_nibble_value(char c)
{
  if (c >= '0' && c <= '9') {
    return c - '0';
  }
  if (c >= 'a' && c <= 'f') {
    return 10 + (c - 'a');
  }
  if (c >= 'A' && c <= 'F') {
    return 10 + (c - 'A');
  }
  return -1;
}

static int parse_hex_byte_strict(const char *s, unsigned char *out)
{
  int hi;
  int lo;

  if (s == NULL || out == NULL) {
    return 0;
  }

  hi = hex_nibble_value(s[0]);
  lo = hex_nibble_value(s[1]);
  if (hi < 0 || lo < 0 || s[2] != '\0') {
    return 0;
  }

  *out = (unsigned char)((hi << 4) | lo);
  return 1;
}

static int parse_can_tx_spec(const char *spec,
                             PASSTHRU_MSG *msg,
                             int *out_is_ext,
                             unsigned long *out_can_id,
                             unsigned long *out_payload_len)
{
  char *work = NULL;
  char *hash = NULL;
  char *id_str = NULL;
  char *len_str = NULL;
  char *payload_str = NULL;
  char *endp = NULL;
  unsigned long can_id;
  unsigned long dlc;
  int is_ext = 0;
  unsigned long parsed_bytes = 0;
  char *tok;
  char *saveptr = NULL;

  if (spec == NULL || msg == NULL) {
    return 0;
  }

  work = strdup(spec);
  if (work == NULL) {
    return 0;
  }

  hash = strchr(work, '#');
  if (hash == NULL) {
    free(work);
    return 0;
  }
  *hash = '\0';

  id_str = work;
  len_str = hash + 1;

  if (id_str[0] == 'e' || id_str[0] == 'E') {
    is_ext = 1;
    id_str++;
  }

  if (*id_str == '\0') {
    free(work);
    return 0;
  }

  can_id = strtoul(id_str, &endp, 16);
  if (endp == id_str || (endp != NULL && *endp != '\0')) {
    free(work);
    return 0;
  }

  if ((!is_ext && can_id > 0x7FFUL) || (is_ext && can_id > 0x1FFFFFFFUL)) {
    free(work);
    return 0;
  }

  while (*len_str != '\0' && isspace((unsigned char)*len_str)) {
    len_str++;
  }
  if (*len_str == '\0') {
    free(work);
    return 0;
  }

  dlc = strtoul(len_str, &endp, 16);
  if (endp == len_str) {
    free(work);
    return 0;
  }
  if (dlc > 8UL) {
    free(work);
    return 0;
  }

  payload_str = endp;
  while (*payload_str != '\0' && isspace((unsigned char)*payload_str)) {
    payload_str++;
  }

  memset(msg, 0, sizeof(*msg));
  msg->ProtocolID = J2534_PROTO_CAN;
  msg->TxFlags = is_ext ? J2534_CAN_29BIT_ID : 0UL;
  msg->DataSize = 4UL + dlc;
  msg->Data[0] = (unsigned char)((can_id >> 24) & 0xFFUL);
  msg->Data[1] = (unsigned char)((can_id >> 16) & 0xFFUL);
  msg->Data[2] = (unsigned char)((can_id >> 8) & 0xFFUL);
  msg->Data[3] = (unsigned char)(can_id & 0xFFUL);

  if (dlc == 0UL) {
    if (*payload_str != '\0') {
      free(work);
      return 0;
    }
  } else {
    tok = strtok_r(payload_str, " \t", &saveptr);
    while (tok != NULL) {
      unsigned char b;
      if (parsed_bytes >= dlc) {
        free(work);
        return 0;
      }
      if (!parse_hex_byte_strict(tok, &b)) {
        free(work);
        return 0;
      }
      msg->Data[4UL + parsed_bytes] = b;
      parsed_bytes++;
      tok = strtok_r(NULL, " \t", &saveptr);
    }

    if (parsed_bytes != dlc) {
      free(work);
      return 0;
    }
  }

  if (out_is_ext != NULL) {
    *out_is_ext = is_ext;
  }
  if (out_can_id != NULL) {
    *out_can_id = can_id;
  }
  if (out_payload_len != NULL) {
    *out_payload_len = dlc;
  }

  free(work);
  return 1;
}

static int32_t send_can_frame(unsigned long channel_id, const PASSTHRU_MSG *msg)
{
  PASSTHRU_MSG tx;
  unsigned long num_msgs = 1;
  int32_t st;

  if (msg == NULL) {
    return J2534_ERR_NULL_PARAMETER;
  }

  memset(&tx, 0, sizeof(tx));
  memcpy(&tx, msg, sizeof(tx));

  st = PassThruWriteMsgs(channel_id, &tx, &num_msgs, 1000UL);
  if (st == J2534_NOERROR && num_msgs != 1UL) {
    return J2534_ERR_FAILED;
  }

  return st;
}

static void sleep_ms_interruptible(unsigned long ms)
{
  struct timespec req;
  struct timespec rem;

  req.tv_sec = (time_t)(ms / 1000UL);
  req.tv_nsec = (long)((ms % 1000UL) * 1000000UL);

  while (!g_stop) {
    if (nanosleep(&req, &rem) == 0) {
      break;
    }
    if (errno != EINTR) {
      break;
    }
    req = rem;
  }
}

static unsigned long long monotonic_time_ms(void)
{
  struct timespec ts;

  if (clock_gettime(CLOCK_MONOTONIC, &ts) != 0) {
    return 0ULL;
  }

  return ((unsigned long long)ts.tv_sec * 1000ULL) +
         ((unsigned long long)ts.tv_nsec / 1000000ULL);
}

static unsigned long compute_read_timeout_ms(int repeat_enabled,
                                             int listen_enabled,
                                             unsigned long long next_send_ms)
{
  unsigned long long now_ms;
  unsigned long long delta_ms;

  if (!listen_enabled) {
    return 0UL;
  }

  if (!repeat_enabled) {
    return READ_TIMEOUT_MS;
  }

  now_ms = monotonic_time_ms();
  if (now_ms >= next_send_ms) {
    return MIN_READ_TIMEOUT_MS;
  }

  delta_ms = next_send_ms - now_ms;
  if (delta_ms > (unsigned long long)READ_TIMEOUT_MS) {
    delta_ms = (unsigned long long)READ_TIMEOUT_MS;
  }

  if (delta_ms == 0ULL) {
    return MIN_READ_TIMEOUT_MS;
  }

  return (unsigned long)delta_ms;
}

static uint32_t be32_to_u32(const unsigned char *p)
{
  return ((uint32_t)p[0] << 24) |
         ((uint32_t)p[1] << 16) |
         ((uint32_t)p[2] << 8) |
         (uint32_t)p[3];
}

static void print_can_frame(const PASSTHRU_MSG *m)
{
  uint32_t raw_id;
  uint32_t can_id;
  unsigned long payload_offset = 4;
  unsigned long payload_len;
  int is_ext = 0;

  if (m == NULL) {
    return;
  }

  if (m->DataSize < 4) {
    printf("RX short msg: DataSize=%lu RxStatus=0x%08lx TxFlags=0x%08lx\n",
           m->DataSize, m->RxStatus, m->TxFlags);
    return;
  }

  raw_id = be32_to_u32(m->Data);
  if ((m->RxStatus & J2534_CAN_29BIT_ID) != 0UL ||
      (m->TxFlags & J2534_CAN_29BIT_ID) != 0UL) {
    is_ext = 1;
  }

  can_id = is_ext ? (raw_id & 0x1FFFFFFFUL) : (raw_id & 0x7FFUL);
  payload_len = m->DataSize - payload_offset;

  printf("ts=%lu proto=%lu %s id=0x%0*lX dlc=%lu data",
         m->Timestamp,
         m->ProtocolID,
         is_ext ? "EXT" : "STD",
         is_ext ? 8 : 3,
         (unsigned long)can_id,
         payload_len);

  for (unsigned long i = 0; i < payload_len; ++i) {
    printf(" %02X", m->Data[payload_offset + i]);
  }

  printf("  [RxStatus=0x%08lx TxFlags=0x%08lx ExtraDataIndex=%lu]\n",
         m->RxStatus, m->TxFlags, m->ExtraDataIndex);
}
static int32_t install_pass_all_filter(unsigned long channelID,
  unsigned long txflags,
  unsigned long *outFilterID)
{
  PASSTHRU_MSG mask;
  PASSTHRU_MSG pattern;
  unsigned long filter_id = 0;

  // memset(&mask, 0, sizeof(mask));
  // memset(&pattern, 0, sizeof(pattern));

  mask.ProtocolID = J2534_PROTO_CAN;
  pattern.ProtocolID = J2534_PROTO_CAN;

  /* ID field only */
  mask.DataSize = 4;
  pattern.DataSize = 4;

  /* PASS_FILTER with mask=0 and pattern=0 matches everything.
    NOTE: this stack uses TxFlags in the filter; for extended frames you
    must set txflags = J2534_CAN_29BIT_ID.
  */
  mask.ProtocolID = J2534_PROTO_CAN;
  mask.TxFlags    = txflags;
  mask.DataSize   = 4;

  pattern.ProtocolID = J2534_PROTO_CAN;
  pattern.TxFlags    = txflags;
  pattern.DataSize   = 4;

  memset(mask.Data, 0, 4);
  memset(pattern.Data, 0, 4);

  int32_t st = PassThruStartMsgFilter(channelID,
    (unsigned long)J2534_PASS_FILTER,
    &mask, &pattern,
    NULL,
    &filter_id);

  if (st == J2534_NOERROR) {
    if (outFilterID)
      *outFilterID = filter_id;
    return J2534_NOERROR;
  }

  /* Helpful debug */
  char desc[256];
  memset(desc, 0, sizeof(desc));
  (void)PassThruGetLastError(desc);
  printf("PassThruStartMsgFilter failed: %d (%s) lastError='%s'\n",
    st, j2534_err_str(st), desc);

  return st;
}

static int bitrate_is_sensible(unsigned long bitrate)
{
  /* OpenPort 2.0 commonly supports these classic CAN rates */
  static const unsigned long allowed[] = {
    10000UL,
    20000UL,
    33333UL,
    50000UL,
    83333UL,
    100000UL,
    125000UL,
    250000UL,
    500000UL,
    800000UL,
    1000000UL,
  };

  for (unsigned int i = 0; i < (sizeof(allowed) / sizeof(allowed[0])); ++i) {
    if (bitrate == allowed[i]) {
      return 1;
    }
  }
  return 0;
}

static void usage(const char *argv0)
{
  printf("Usage: %s [options] [device_name|-] [std|ext|both]\n", argv0);
  printf("       %s [options] -s \"[e]CANID#LEN[ aa bb cc ...]\" [device_name|-]\n", argv0);
  printf("\n");
  printf("Options:\n");
  printf("  -h, --help                 Show this help and exit\n");
  printf("  -b, --bitrate <rate>       CAN bitrate (default 500000)\n");
  printf("                             Allowed: 10000, 20000, 33333, 50000, 83333,\n");
  printf("                                      100000, 125000, 250000, 500000,\n");
  printf("                                      800000, 1000000\n");
  printf("  -s, --send <frame>         Send CAN frame\n");
  printf("  -r, --repeat <ms>          With -s, keep sending every N milliseconds\n");
  printf("  -l, --listen               With -s, also receive/print RX frames\n");
  printf("                             Frame format: [e]CANID#LEN[ data...]\n");
  printf("                             All fields are hex. Prefix ID with 'e' for\n");
  printf("                             an extended frame. LEN is 0..8. Each payload\n");
  printf("                             byte must be 2 hex digits separated by spaces.\n");
  printf("\n");
  printf("Arguments:\n");
  printf("  device_name                 Optional string passed to PassThruOpen(pName,...)\n");
  printf("                              Use '-' to pass NULL (default device)\n");
  printf("  std|ext|both                Receive mode only (default: both)\n");
  printf("                               std  : 11-bit only\n");
  printf("                               ext  : 29-bit only\n");
  printf("                               both : receive both 11/29-bit\n");
  printf("\n");
  printf("Examples:\n");
  printf("  %s -h\n", argv0);
  printf("  %s -b 500000 tactrix_0 both\n", argv0);
  printf("  %s -b 250000 - ext\n", argv0);
  printf("  %s -s \"123#3 01 AB FF\" tactrix_0\n", argv0);
  printf("  %s -s \"e18DAF110#8 02 10 03 00 00 00 00 00\" -\n", argv0);
  printf("  %s -s \"123#2 01 02\" -r 1000 -\n", argv0);
}

int main(int argc, char **argv)
{
  int32_t status;
  unsigned long device_id = 0;
  unsigned long channel_id = 0;

  unsigned long fid_std = 0;
  //unsigned long fid_ext = 0;
  const void *device_name = NULL;
  const char *mode = "both";
  const char *send_spec = NULL;
  int listen_while_sending = 0;
  unsigned long repeat_ms = 0UL;
  unsigned long connect_flags = 0UL;
  unsigned long bitrate = DEFAULT_BITRATE;
  PASSTHRU_MSG txmsg;
  int exit_code = 0;
  int tx_is_ext = 0;
  unsigned long tx_can_id = 0UL;
  unsigned long tx_payload_len = 0UL;

  /* Parse options */
  int argi = 1;
  while (argi < argc) {
    const char *a = argv[argi];
    if (a == NULL) {
      argi++;
      continue;
    }

    if (strcmp(a, "-h") == 0 || strcmp(a, "--help") == 0) {
      usage(argv[0]);
      return 0;
    }

    if (strcmp(a, "-b") == 0 || strcmp(a, "--bitrate") == 0) {
      if (argi + 1 >= argc) {
        printf("Missing value after %s\n", a);
        usage(argv[0]);
        return 2;
      }
      const char *v = argv[argi + 1];
      char *endp = NULL;
      unsigned long br = strtoul(v, &endp, 10);
      if (endp == v || (endp != NULL && *endp != '\0')) {
        printf("Invalid bitrate: %s\n", v);
        usage(argv[0]);
        return 2;
      }
      if (!bitrate_is_sensible(br)) {
        printf("Bitrate not allowed/sensible for this test: %lu\n", br);
        usage(argv[0]);
        return 2;
      }
      bitrate = br;
      argi += 2;
      continue;
    }

    if (strcmp(a, "-s") == 0 || strcmp(a, "--send") == 0) {
      if (argi + 1 >= argc) {
        printf("Missing value after %s\n", a);
        usage(argv[0]);
        return 2;
      }
      send_spec = argv[argi + 1];
      argi += 2;
      continue;
    }

    if (strcmp(a, "-l") == 0 || strcmp(a, "--listen") == 0) {
      listen_while_sending = 1;
      argi += 1;
      continue;
    }

    if (strcmp(a, "-r") == 0 || strcmp(a, "--repeat") == 0) {
      if (argi + 1 >= argc) {
        printf("Missing value after %s\n", a);
        usage(argv[0]);
        return 2;
      }
      const char *v = argv[argi + 1];
      char *endp = NULL;
      unsigned long val = strtoul(v, &endp, 10);
      if (endp == v || (endp != NULL && *endp != '\0') || val == 0UL) {
        printf("Invalid repeat interval in milliseconds: %s\n", v);
        usage(argv[0]);
        return 2;
      }
      repeat_ms = val;
      argi += 2;
      continue;
    }

    if (a[0] == '-' && a[1] != '\0') {
      printf("Unknown option: %s\n", a);
      usage(argv[0]);
      return 2;
    }

    /* First non-option is positional */
    break;
  }

  /* Positional: device_name */
  if (argi < argc) {
    const char *dn = argv[argi++];
    if (dn != NULL && dn[0] != '\0' && strcmp(dn, "-") != 0) {
      device_name = dn;
    } else {
      device_name = NULL;
    }
  }

  /* Positional: mode */
  if (argi < argc) {
    const char *m = argv[argi++];
    if (m != NULL && m[0] != '\0') {
      mode = m;
    }
  }

  if (argi < argc) {
    printf("Unexpected extra argument: %s\n", argv[argi]);
    usage(argv[0]);
    return 2;
  }

  if (repeat_ms != 0UL && send_spec == NULL) {
    printf("--repeat/-r may only be used together with --send/-s\n");
    usage(argv[0]);
    return 2;
  }

  if (listen_while_sending && send_spec == NULL) {
    printf("--listen/-l may only be used together with --send/-s\n");
    usage(argv[0]);
    return 2;
  }

  if (strcmp(mode, "std") == 0) {
    connect_flags = 0UL;
  } else if (strcmp(mode, "ext") == 0) {
    connect_flags = J2534_CAN_29BIT_ID;
  } else if (strcmp(mode, "both") == 0) {
    connect_flags = J2534_CAN_29BIT_ID | J2534_CAN_ID_BOTH;
  } else {
    printf("Unknown mode: %s\n", mode);
    usage(argv[0]);
    return 2;
  }

  if (send_spec != NULL) {
    if (!parse_can_tx_spec(send_spec, &txmsg, &tx_is_ext, &tx_can_id, &tx_payload_len)) {
      printf("Invalid CAN frame for --send: %s\n", send_spec);
      usage(argv[0]);
      return 2;
    }

    if (!listen_while_sending) {
      connect_flags = tx_is_ext ? J2534_CAN_29BIT_ID : 0UL;
    } else {
      if (strcmp(mode, "std") == 0 && tx_is_ext) {
        printf("Cannot send an extended CAN frame while receive mode is 'std'\n");
        usage(argv[0]);
        return 2;
      }
      if (strcmp(mode, "ext") == 0 && !tx_is_ext) {
        printf("Cannot send a standard CAN frame while receive mode is 'ext'\n");
        usage(argv[0]);
        return 2;
      }
    }
  }

  signal(SIGINT, on_sigint);

  printf("Opening device (name=%s)...\n",
         device_name ? (const char *)device_name : "NULL");
  status = PassThruOpen(device_name, &device_id);
  if (status != J2534_NOERROR) {
    printf("PassThruOpen failed: %d (%s)\n", status, j2534_err_str(status));
    print_last_error_if_any();
    return 1;
  }
  printf("Opened device_id=%lu\n", device_id);

  char api_ver[128] = {0};
  char solib_ver[128] = {0};
  char fw_ver[128] = {0};

  status = PassThruReadVersion(device_id, fw_ver, solib_ver, api_ver);
  if (status != J2534_NOERROR) {
    printf("PassThruReadVersion failed: %d (%s)\n", status, j2534_err_str(status));
    print_last_error_if_any();
  }
  else {
    printf("API version: %s\n", api_ver);
    printf("DLL version: %s\n", solib_ver);
    printf("Firmware version: %s\n", fw_ver);
  }

  printf("Connecting raw CAN at %lu bps (flags=0x%08lx%s%s)...\n",
         bitrate, connect_flags,
         send_spec ? ", send=" : ", mode=",
         send_spec ? send_spec : mode);
  status = PassThruConnect(device_id,
                           J2534_PROTO_CAN,
                           connect_flags,
                           bitrate,
                           &channel_id);
  if (status != J2534_NOERROR) {
    printf("PassThruConnect failed: %d (%s)\n", status, j2534_err_str(status));
    print_last_error_if_any();
    (void)PassThruClose(device_id);
    return 1;
  }
  printf("Connected channel_id=%lu\n", channel_id);

  /* Explicitly disable J2534 loopback/echo on this channel */
  {
    /* This was to try prevent Tactrix/OpenPort2.0 returning every TX'ed frame as RX (no other flags).
     * Unfortunately this doesnt' do it, but does not hurt either: if loopback is enabled you endup
     * seeing your TX at least x2...*/
    
    SCONFIG cfg;
    SCONFIG_LIST cfg_list;
    unsigned long got = 0UL;

    cfg.Parameter = J2534_LOOPBACK;
    cfg.Value = J2534_OFF;

    cfg_list.NumOfParams = 1;
    cfg_list.ConfigPtr = &cfg;

    status = PassThruIoctl(channel_id, J2534_SET_CONFIG, &cfg_list, NULL);
    if (status != J2534_NOERROR) {
      printf("SET_CONFIG(LOOPBACK=0) failed: %d (%s)\n",
            status, j2534_err_str(status));
      print_last_error_if_any();
    } else {
      printf("SET_CONFIG(LOOPBACK=0) OK\n");
    }

    cfg.Parameter = J2534_LOOPBACK;
    cfg.Value = 0UL;
    cfg_list.NumOfParams = 1;
    cfg_list.ConfigPtr = &cfg;

    status = PassThruIoctl(channel_id, J2534_GET_CONFIG, &cfg_list, NULL);
    if (status != J2534_NOERROR) {
      printf("GET_CONFIG(LOOPBACK) failed: %d (%s)\n",
            status, j2534_err_str(status));
      print_last_error_if_any();
    } else {
      got = cfg.Value;
      printf("GET_CONFIG(LOOPBACK) -> %lu\n", got);
    }
  }

  if (send_spec != NULL) {
    unsigned long send_count = 0UL;
    int listening_active = 0;
    unsigned long long next_send_ms = 0ULL;

    printf("Sending %s CAN frame: id=0x%0*lX dlc=%lu",
           tx_is_ext ? "EXT" : "STD",
           tx_is_ext ? 8 : 3,
           tx_can_id,
           tx_payload_len);
    for (unsigned long i = 0; i < tx_payload_len; ++i) {
      printf(" %02X", txmsg.Data[4UL + i]);
    }
    printf("\n");

    if (listen_while_sending) {
      status = install_pass_all_filter(channel_id, 0, &fid_std);
      if (status != J2534_NOERROR) {
        (void)PassThruDisconnect(channel_id);
        (void)PassThruClose(device_id);
        printf("Failed to install pass-all filter with 11-bit IDs\n");
        return 1;
      }
      listening_active = 1;
      printf("Filter installed (pass-all std): =%lu\n", fid_std);
      printf("Listening for incoming CAN frames while sending... (Ctrl+C to stop)\n");
    }

    if (repeat_ms != 0UL) {
      printf("Repeat send enabled: every %lu ms%s\n",
             repeat_ms,
             listen_while_sending ? " with RX polling (Ctrl+C to stop)" : " (Ctrl+C to stop)");

      next_send_ms = monotonic_time_ms();
      while (!g_stop) {
        unsigned long long now_ms = monotonic_time_ms();

        if (now_ms >= next_send_ms) {
          status = send_can_frame(channel_id, &txmsg);
          if (status != J2534_NOERROR) {
            printf("PassThruWriteMsgs failed: %d (%s)\n", status, j2534_err_str(status));
            print_last_error_if_any();
            exit_code = 1;
            goto cleanup;
          }
          send_count++;
          next_send_ms = now_ms + (unsigned long long)repeat_ms;
          continue;
        }

        if (listen_while_sending) {
          PASSTHRU_MSG msgs[8];
          unsigned long num_msgs = 8;
          unsigned long timeout_ms = compute_read_timeout_ms(1, 1, next_send_ms);

          memset(msgs, 0, sizeof(msgs));
          status = PassThruReadMsgs(channel_id, msgs, &num_msgs, timeout_ms);
          if (status == J2534_ERR_TIMEOUT) {
            continue;
          }
          if (status != J2534_NOERROR) {
            printf("PassThruReadMsgs failed: %d (%s), num_msgs=%lu\n",
                   status, j2534_err_str(status), num_msgs);
            print_last_error_if_any();
            exit_code = 1;
            goto cleanup;
          }
          for (unsigned long i = 0; i < num_msgs; ++i) {
            printf("RX: ");
            print_can_frame(&msgs[i]);
          }
        } else {
          sleep_ms_interruptible((unsigned long)(next_send_ms - now_ms));
        }
      }
      printf("Stopped after %lu sends.\n", send_count);
    } else {
      status = send_can_frame(channel_id, &txmsg);
      if (status != J2534_NOERROR) {
        printf("PassThruWriteMsgs failed: %d (%s)\n", status, j2534_err_str(status));
        print_last_error_if_any();
        exit_code = 1;
        goto cleanup;
      }
      send_count++;
      printf("Send OK.\n");

      while (listen_while_sending && !g_stop) {
        PASSTHRU_MSG msgs[8];
        unsigned long num_msgs = 8;

        memset(msgs, 0, sizeof(msgs));
        status = PassThruReadMsgs(channel_id, msgs, &num_msgs, READ_TIMEOUT_MS);
        if (status == J2534_ERR_TIMEOUT) {
          continue;
        }
        if (status != J2534_NOERROR) {
          printf("PassThruReadMsgs failed: %d (%s), num_msgs=%lu\n",
                 status, j2534_err_str(status), num_msgs);
          print_last_error_if_any();
          exit_code = 1;
          goto cleanup;
        }
        for (unsigned long i = 0; i < num_msgs; ++i) {
          print_can_frame(&msgs[i]);
        }
      }
    }

cleanup:
    if (listening_active && fid_std != 0UL) {
      int32_t stop_status = PassThruStopMsgFilter(channel_id, fid_std);
      if (stop_status != J2534_NOERROR) {
        printf("PassThruStopMsgFilter failed: %d (%s)\n",
               stop_status, j2534_err_str(stop_status));
        print_last_error_if_any();
      }
    }

    status = PassThruDisconnect(channel_id);
    if (status != J2534_NOERROR) {
      printf("PassThruDisconnect failed: %d (%s)\n",
             status, j2534_err_str(status));
      print_last_error_if_any();
      (void)PassThruClose(device_id);
      return 1;
    }

    status = PassThruClose(device_id);
    if (status != J2534_NOERROR) {
      printf("PassThruClose failed: %d (%s)\n", status, j2534_err_str(status));
      print_last_error_if_any();
      return 1;
    }

    printf("Done.\n");
    return exit_code;
  }

  /* Install pass-all filter */
  status = install_pass_all_filter(channel_id, 0, &fid_std);
  if (status != J2534_NOERROR) {
    (void)PassThruDisconnect(channel_id);
    (void)PassThruClose(device_id);
    printf("Failed to install pass-all filter with 11-bit IDs\n");
    return 1;
  }
  printf("Filter installed (pass-all std): =%lu\n", fid_std);

  /* NOTE: seems with Tactrix as long as you connected with both-can-IDs flags
   * second filter does nothing, you will get std and ext CAN-ID'ed frames.
  status = install_pass_all_filter(channel_id, J2534_CAN_29BIT_ID, &fid_ext);
  if (status != J2534_NOERROR) {
    (void)PassThruDisconnect(channel_id);
    (void)PassThruClose(device_id);
    printf("Failed to install pass-all filter with 29-bit IDs\n");
    return 1;
  }
  */

  printf("Listening for incoming CAN frames... (Ctrl+C to stop)\n");
  while (!g_stop) {
    PASSTHRU_MSG msgs[8];
    unsigned long num_msgs = 8;

    memset(msgs, 0, sizeof(msgs));

    status = PassThruReadMsgs(channel_id, msgs, &num_msgs, 200UL);

    if (status == J2534_ERR_TIMEOUT) {
      continue;
    }

    if (status != J2534_NOERROR) {
      printf("PassThruReadMsgs failed: %d (%s), num_msgs=%lu\n",
             status, j2534_err_str(status), num_msgs);
      print_last_error_if_any();
      break;
    }

    for (unsigned long i = 0; i < num_msgs; ++i) {
      print_can_frame(&msgs[i]);
    }
  }

  printf("Stopping...\n");

  status = PassThruStopMsgFilter(channel_id, fid_std);
  if (status != J2534_NOERROR) {
    printf("PassThruStopMsgFilter failed: %d (%s)\n",
           status, j2534_err_str(status));
    print_last_error_if_any();
  }

  status = PassThruDisconnect(channel_id);
  if (status != J2534_NOERROR) {
    printf("PassThruDisconnect failed: %d (%s)\n",
           status, j2534_err_str(status));
    print_last_error_if_any();
  }

  status = PassThruClose(device_id);
  if (status != J2534_NOERROR) {
    printf("PassThruClose failed: %d (%s)\n", status, j2534_err_str(status));
    print_last_error_if_any();
    return 1;
  }

  printf("Done.\n");
  return 0;
}
