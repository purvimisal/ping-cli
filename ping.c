// PING allows -c and -t options 

// Compile with: gcc -o ping ping.c
// Run with : ping [-c count] [-t ttl] host_address \n")

#include <sys/param.h>
#include <sys/socket.h>
#include <sys/file.h>
#include <sys/time.h>
#include <sys/signal.h>
#include <netinet/in.h>
#include <netinet/ip.h>
#include <netinet/ip_icmp.h>
#include <arpa/inet.h>
#include <netdb.h>
#include <unistd.h>
#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#include <ctype.h>
#include <errno.h>

#define icmphdr			icmp
#define ICMP_DEST_UNREACH	ICMP_UNREACH

#define	DEFDATALEN	(64 - 8)	
#define	MAXIPLEN	60
#define	MAXICMPLEN	76
#define	MAXPACKET	(65536 - 60 - 8)
#define	MAXWAIT		10		
#define	NROUTES		9		

#define	A(bit)		rcvd_tbl[(bit)>>3]	
#define	B(bit)		(1 << ((bit) & 0x07))	
#define	SET(bit)	(A(bit) |= B(bit))
#define	CLR(bit)	(A(bit) &= (~B(bit)))
#define	TST(bit)	(A(bit) & B(bit))

int options;
#define	F_FLOOD		0x001
#define	F_QUIET		0x010
#define	F_VERBOSE	0x100

int moptions;
#define MULTICAST_TTL		0x002

#define	MAX_DUP_CHK	(8 * 128)
int mx_dup_ck = MAX_DUP_CHK;
char rcvd_tbl[MAX_DUP_CHK / 8];

struct sockaddr whereto;	
int datalen = DEFDATALEN;
int s;				
u_char outpack[MAXPACKET];
char BSPACE = '\b';		
char DOT = '.';
static char *hostname;
static int ident;		

//counter
static long npackets;		
static long nreceived;		
static long nrepeats;		
static long ntransmitted;	
static int interval = 1;	

// for timing
static int timing;		
static long tmin = LONG_MAX;	
static long tmax = 0;	
static u_long tsum;	

//protocol requirements
static char *pr_addr(u_long);
static int in_cksum(u_short *addr, int len);
static void catcher(int);
static void finish(int ignore);
static void pinger(void);
// static void fill(void *bp, char *patp);
static void usage(void);
static void pr_pack(char *buf, int cc, struct sockaddr_in *from);
static void tvsub(struct timeval *out, struct timeval *in);
static void pr_icmph(struct icmphdr *icp);
// static void pr_retip(struct iphdr *ip);


int main(int argc, char *argv[])
{
	struct timeval timeout;
	struct hostent *hp;
	struct sockaddr_in *to;
	struct protoent *proto;
	struct in_addr ifaddr;
	int i;
	int ch, fdmask, hold, packlen, preload;
	u_char *datap, *packet;
	char *target, hnamebuf[MAXHOSTNAMELEN];
	u_char ttl, loop;
	int am_i_root;
#ifdef IP_OPTIONS
	char rspace[3 + 4 * NROUTES + 1];	/* record route space */
#endif
	static char *null = NULL;
	__environ = &null;
	am_i_root = (getuid()==0);

	if (!(proto = getprotobyname("icmp"))) {
		(void)fprintf(stderr, "ping: unknown protocol icmp.\n");
		exit(2);
	}
	if ((s = socket(AF_INET, SOCK_RAW, proto->p_proto)) < 0) {
		if (errno==EPERM) {
			fprintf(stderr, "ping: ping must run as root\n");
		}
		else perror("ping: socket");
		exit(2);
	}
	preload = 0;
	datap = &outpack[8 + sizeof(struct timeval)];
	while ((ch = getopt(argc, argv, "I:LRc:dfh:i:l:np:qrs:t:v")) != EOF)
		switch(ch) {
		case 'c':
			npackets = atoi(optarg);
			if (npackets <= 0) {
				(void)fprintf(stderr,
				    "ping: bad number of packets to transmit.\n");
				exit(2);
			}
			break;
		case 't':
			moptions |= MULTICAST_TTL;
			i = atoi(optarg);
			if (i < 0 || i > 255) {
				printf("ttl %u out of range\n", i);
				exit(2);
			}
			ttl = i;
			break;
		default:
			usage();
		}
	argc -= optind;
	argv += optind;
	
	if (argc != 1)
		usage();
	target = *argv;

	memset(&whereto, 0, sizeof(struct sockaddr));
	to = (struct sockaddr_in *)&whereto;
	to->sin_family = AF_INET;
	if (inet_aton(target, &to->sin_addr)) {
		hostname = target;
	}
	else {
		hp = gethostbyname(target);
		if (!hp) {
			(void)fprintf(stderr,
			    "ping: unknown host %s\n", target);
			exit(2);
		}
		to->sin_family = hp->h_addrtype;
		if (hp->h_length > (int)sizeof(to->sin_addr)) {
			hp->h_length = sizeof(to->sin_addr);
		}
		memcpy(&to->sin_addr, hp->h_addr, hp->h_length);
		(void)strncpy(hnamebuf, hp->h_name, sizeof(hnamebuf) - 1);
		hostname = hnamebuf;
	}


	if (datalen >= (int)sizeof(struct timeval)) /* can we time transfer */
		timing = 1;
	packlen = datalen + MAXIPLEN + MAXICMPLEN;
	packet = malloc((u_int)packlen);
	if (!packet) {
		(void)fprintf(stderr, "ping: out of memory.\n");
		exit(2);
	}
		for (i = 8; i < datalen; ++i)
			*datap++ = i;

	ident = getpid() & 0xFFFF;
	hold = 1;

	setsockopt(s, SOL_SOCKET, SO_BROADCAST, (char *)&hold, sizeof(hold));


	hold = 48 * 1024;
	(void)setsockopt(s, SOL_SOCKET, SO_RCVBUF, (char *)&hold,
	    sizeof(hold));

	if (moptions & MULTICAST_TTL) {
		if (setsockopt(s, IPPROTO_IP, IP_MULTICAST_TTL,
							&ttl, 1) == -1) {
			perror ("can't set multicast time-to-live");
			exit(93);
		}
	}

	if (to->sin_family == AF_INET)
		(void)printf("PING %s (%s): %d data bytes\n", hostname,
		    inet_ntoa(*(struct in_addr *)&to->sin_addr.s_addr),
		    datalen);
	else
		(void)printf("PING %s: %d data bytes\n", hostname, datalen);

	(void)signal(SIGINT, finish);
	(void)signal(SIGALRM, catcher);

	while (preload--)		/* fire off them quickies */
		pinger();

	if ((options & F_FLOOD) == 0)
		catcher(0);		/* start things going */

	for (;;) {
		struct sockaddr_in from;
		register int cc;
		size_t fromlen;

		if (options & F_FLOOD) {
			pinger();
			timeout.tv_sec = 0;
			timeout.tv_usec = 10000;
			fdmask = 1 << s;
			if (select(s + 1, (fd_set *)&fdmask, (fd_set *)NULL,
			    (fd_set *)NULL, &timeout) < 1)
				continue;
		}
		fromlen = sizeof(from);
		if ((cc = recvfrom(s, (char *)packet, packlen, 0,
		    (struct sockaddr *)&from, &fromlen)) < 0) {
			if (errno == EINTR)
				continue;
			perror("ping: recvfrom");
			continue;
		}
		pr_pack((char *)packet, cc, &from);
		if (npackets && nreceived >= npackets)
			break;
	}
	finish(0);
	return 0;
}


static void catcher(int ignore)
{
	int waittime;

	(void)ignore;
	pinger();
	(void)signal(SIGALRM, catcher);
	if (!npackets || ntransmitted < npackets)
		alarm((u_int)interval);
	else {
		if (nreceived) {
			waittime = 2 * tmax / 1000;
			if (!waittime)
				waittime = 1;
			if (waittime > MAXWAIT)
				waittime = MAXWAIT;
		} else
			waittime = MAXWAIT;
		(void)signal(SIGALRM, finish);
		(void)alarm((u_int)waittime);
	}
}

#if !defined(__GLIBC__) || (__GLIBC__ < 2)
#define icmp_type type
#define icmp_code code
#define icmp_cksum checksum
#define icmp_id un.echo.id
#define icmp_seq un.echo.sequence
#define icmp_gwaddr un.gateway
#endif /* __GLIBC__ */

#define ip_hl ihl
#define ip_v version
#define ip_tos tos
#define ip_len tot_len
#define ip_id id
#define ip_off frag_off
#define ip_ttl ttl
#define ip_p protocol
#define ip_sum check
#define ip_src saddr
#define ip_dst daddr

static void pinger(void)
{
	register struct icmphdr *icp;
	register int cc;
	int i;

	icp = (struct icmphdr *)outpack;
	icp->icmp_type = ICMP_ECHO;
	icp->icmp_code = 0;
	icp->icmp_cksum = 0;
	icp->icmp_seq = ntransmitted++;
	icp->icmp_id = ident;		

	CLR(icp->icmp_seq % mx_dup_ck);

	if (timing)
		(void)gettimeofday((struct timeval *)&outpack[8],
		    (struct timezone *)NULL);

	cc = datalen + 8;		

	icp->icmp_cksum = in_cksum((u_short *)icp, cc);

	i = sendto(s, (char *)outpack, cc, 0, &whereto,
	    sizeof(struct sockaddr));

	if (i < 0 || i != cc)  {
		if (i < 0)
			perror("ping: sendto");
		(void)printf("ping: wrote %s %d chars, ret=%d\n",
		    hostname, cc, i);
	}
	if (!(options & F_QUIET) && options & F_FLOOD)
		(void)write(STDOUT_FILENO, &DOT, 1);
}


void pr_pack(char *buf, int cc, struct sockaddr_in *from)
{
	register struct icmphdr *icp;
	register int i;
	register u_char *cp,*dp;
	register u_long l;
	register int j;
	static int old_rrlen;
	static char old_rr[MAX_IPOPTLEN];
	struct iphdr *ip;
	struct timeval tv, *tp;
	long triptime = 0;
	int hlen, dupflag;

	(void)gettimeofday(&tv, (struct timezone *)NULL);

	//Checking IP header
	ip = (struct iphdr *)buf;
	hlen = ip->ip_hl << 2;
	if (cc < datalen + ICMP_MINLEN) {
		if (options & F_VERBOSE)
			(void)fprintf(stderr,
			  "ping: packet too short (%d bytes) from %s\n", cc,
			  inet_ntoa(*(struct in_addr *)&from->sin_addr.s_addr));
		return;
	}

	cc -= hlen;
	icp = (struct icmphdr *)(buf + hlen);
	if (icp->icmp_type == ICMP_ECHOREPLY) {
		if (icp->icmp_id != ident)
			return;			
		++nreceived;
		if (timing) {
#ifndef icmp_data
			tp = (struct timeval *)(icp + 1);
#else
			tp = (struct timeval *)icp->icmp_data;
#endif
			tvsub(&tv, tp);
			triptime = tv.tv_sec * 10000 + (tv.tv_usec / 100);
			tsum += triptime;
			if (triptime < tmin)
				tmin = triptime;
			if (triptime > tmax)
				tmax = triptime;
		}

		if (TST(icp->icmp_seq % mx_dup_ck)) {
			++nrepeats;
			--nreceived;
			dupflag = 1;
		} else {
			SET(icp->icmp_seq % mx_dup_ck);
			dupflag = 0;
		}

		if (options & F_FLOOD)
			(void)write(STDOUT_FILENO, &BSPACE, 1);
		else {
			(void)printf("%d bytes from %s: icmp_seq=%u", cc,
			   inet_ntoa(*(struct in_addr *)&from->sin_addr.s_addr),
			   icp->icmp_seq);
			(void)printf(" ttl=%d", ip->ip_ttl);
			if (timing)
				(void)printf(" time=%ld.%ld ms", triptime/10,
						triptime%10);
			if (dupflag)
				(void)printf(" (DUP!)");
			/* check the data */
#ifndef icmp_data
			cp = ((u_char*)(icp + 1) + 8);
#else
			cp = (u_char*)icp->icmp_data + 8;
#endif
			dp = &outpack[8 + sizeof(struct timeval)];
			for (i = 8; i < datalen; ++i, ++cp, ++dp) {
				if (*cp != *dp) {
					cp = (u_char*)(icp + 1);
					for (i = 8; i < datalen; ++i, ++cp) {
						if ((i % 32) == 8)
							(void)printf("\n\t");
						(void)printf("%x ", *cp);
					}
					break;
				}
			}
		}
	} else {
		(void)printf("%d bytes from %s: ", cc,
		    pr_addr(from->sin_addr.s_addr));
		pr_icmph(icp);
	}

	cp = (u_char *)buf + sizeof(struct iphdr);
	for (; hlen > (int)sizeof(struct iphdr); --hlen, ++cp)
		switch (*cp) {
		case IPOPT_EOL:
			hlen = 0;
			break;
		case IPOPT_RR:
			j = *++cp;		
			i = *++cp;		
			hlen -= 2;
			if (i > j)
				i = j;
			i -= IPOPT_MINOFF;
			if (i <= 0)
				continue;
			if (i == old_rrlen
			    && cp == (u_char *)buf + sizeof(struct iphdr) + 2
			    && !memcmp((char *)cp, old_rr, i)
			    && !(options & F_FLOOD)) {
				(void)printf("\t(same route)");
				i = ((i + 3) / 4) * 4;
				hlen -= i;
				cp += i;
				break;
			}
			old_rrlen = i;
			memcpy(old_rr, cp, i);
			(void)printf("\nRR: ");
			for (;;) {
				l = *++cp;
				l = (l<<8) + *++cp;
				l = (l<<8) + *++cp;
				l = (l<<8) + *++cp;
				if (l == 0)
					(void)printf("\t0.0.0.0");
				else
					(void)printf("\t%s", pr_addr(ntohl(l)));
				hlen -= 4;
				i -= 4;
				if (i <= 0)
					break;
				(void)putchar('\n');
			}
			break;
		case IPOPT_NOP:
			(void)printf("\nNOP");
			break;
		default:
			(void)printf("\nunknown option %x", *cp);
			break;
		}
		(void)putchar('\n');
		(void)fflush(stdout);
}

// Checksum function for IP
static int in_cksum(u_short *addr, int len)
{
	register int nleft = len;
	register u_short *w = addr;
	register int sum = 0;
	u_short answer = 0;
	while (nleft > 1)  {
		sum += *w++;
		nleft -= 2;
	}
	if (nleft == 1) {
		*(u_char *)(&answer) = *(u_char *)w ;
		sum += answer;
	}
	sum = (sum >> 16) + (sum & 0xffff);
	sum += (sum >> 16);			
	answer = ~sum;			
	return(answer);
}


static void tvsub(register struct timeval *out, register struct timeval *in)
{
	if ((out->tv_usec -= in->tv_usec) < 0) {
		--out->tv_sec;
		out->tv_usec += 1000000;
	}
	out->tv_sec -= in->tv_sec;
}

static void finish(int ignore)
{
	(void)ignore;

	(void)signal(SIGINT, SIG_IGN);
	(void)putchar('\n');
	(void)fflush(stdout);
	(void)printf("--- %s ping statistics ---\n", hostname);
	(void)printf("%ld packets transmitted, ", ntransmitted);
	(void)printf("%ld packets received, ", nreceived);
	if (nrepeats)
		(void)printf("+%ld duplicates, ", nrepeats);
	if (ntransmitted)
		if (nreceived > ntransmitted)
			(void)printf("-- somebody's printing up packets!");
		else
			(void)printf("%d%% packet loss",
			    (int) (((ntransmitted - nreceived) * 100) /
			    ntransmitted));
	(void)putchar('\n');
	if (nreceived && timing)
		(void)printf("min = %ld.%ld ms|| avg =%lu.%ld ms|| max = %ld.%ld ms\n",
			tmin/10, tmin%10,
			(tsum / (nreceived + nrepeats))/10,
			(tsum / (nreceived + nrepeats))%10,
			tmax/10, tmax%10);

	if (nreceived==0) exit(1);
	exit(0);
}

static void pr_icmph(struct icmphdr *icp)
{
	switch(icp->icmp_type) {
	case ICMP_ECHOREPLY:
		(void)printf("Echo Reply\n");
		break;
	case ICMP_DEST_UNREACH:
		(void)printf("Dest Unreachable, Unknown Code: %d\n",
			    icp->icmp_code);

	default:
		(void)printf("Bad ICMP type: %d\n", icp->icmp_type);
	}
}

static char * pr_addr(u_long l)
{
	struct hostent *hp;
	static char buf[256];

		(void)snprintf(buf, sizeof(buf), "%s (%s)", hp->h_name,
		    inet_ntoa(*(struct in_addr *)&l));
}

static void usage(void)
{
	(void)fprintf(stderr,
	    "usage: ping [-c count] [-t ttl] host_address\n");
	exit(2);
}
