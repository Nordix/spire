package util

import (
	"context"
	"flag"
	"fmt"
	"strings"

	loggerv1 "github.com/spiffe/spire-api-sdk/proto/spire/api/agent/logger/v1"
	api_types "github.com/spiffe/spire-api-sdk/proto/spire/api/types"
	common_cli "github.com/spiffe/spire/pkg/common/cli"
	"google.golang.org/grpc"
	"google.golang.org/grpc/credentials/insecure"
	"google.golang.org/grpc/health/grpc_health_v1"
)

const (
	DefaultSocketPath    = "/tmp/spire-agent/private/api.sock"
	DefaultNamedPipeName = "\\spire-agent\\private\\api"
)

func NewGRPCClient(addr string) (*grpc.ClientConn, error) {
	return grpc.NewClient(
		addr,
		grpc.WithTransportCredentials(insecure.NewCredentials()),
		grpc.WithContextDialer(dialer),
	)
}

type AgentClient interface {
	Release()
	NewLoggerClient() loggerv1.LoggerClient
	NewHealthClient() grpc_health_v1.HealthClient
}

func NewAgentClient(addr string) (AgentClient, error) {
	conn, err := NewGRPCClient(addr)
	if err != nil {
		return nil, err
	}
	return &agentClient{conn: conn}, nil
}

type agentClient struct {
	conn *grpc.ClientConn
}

func (c *agentClient) Release() {
	c.conn.Close()
}

func (c *agentClient) NewLoggerClient() loggerv1.LoggerClient {
	return loggerv1.NewLoggerClient(c.conn)
}

func (c *agentClient) NewHealthClient() grpc_health_v1.HealthClient {
	return grpc_health_v1.NewHealthClient(c.conn)
}

// Pluralizer concatenates `singular` to `msg` when `val` is one, and
// `plural` on all other occasions. It is meant to facilitate friendlier
// CLI output.
func Pluralizer(msg string, singular string, plural string, val int) string {
	result := msg
	if val == 1 {
		result += singular
	} else {
		result += plural
	}

	return result
}

// Command is a common interface for commands in this package. the adapter
// can adapter this interface to the Command interface from github.com/mitchellh/cli.
type Command interface {
	Name() string
	Synopsis() string
	AppendFlags(*flag.FlagSet)
	Run(context.Context, *common_cli.Env, AgentClient) error
}

type Adapter struct {
	env *common_cli.Env
	cmd Command

	flags *flag.FlagSet

	adapterOS // OS specific
}

// AdaptCommand converts a command into one conforming to the Command interface from github.com/mitchellh/cli
func AdaptCommand(env *common_cli.Env, cmd Command) *Adapter {
	a := &Adapter{
		cmd: cmd,
		env: env,
	}

	f := flag.NewFlagSet(cmd.Name(), flag.ContinueOnError)
	f.SetOutput(env.Stderr)
	a.addOSFlags(f)
	a.cmd.AppendFlags(f)
	a.flags = f

	return a
}

func (a *Adapter) Run(args []string) int {
	ctx := context.Background()

	if err := a.flags.Parse(args); err != nil {
		return 1
	}

	addr := a.getGRPCAddr()
	client, err := NewAgentClient(addr)
	if err != nil {
		fmt.Fprintln(a.env.Stderr, "Error: "+err.Error())
		return 1
	}
	defer client.Release()

	if err := a.cmd.Run(ctx, a.env, client); err != nil {
		fmt.Fprintln(a.env.Stderr, "Error: "+err.Error())
		return 1
	}

	return 0
}

func (a *Adapter) Help() string {
	return a.flags.Parse([]string{"-h"}).Error()
}

func (a *Adapter) Synopsis() string {
	return a.cmd.Synopsis()
}

// parseSelector parses a CLI string from type:value into a selector type.
// Everything to the right of the first ":" is considered a selector value.
func ParseSelector(str string) (*api_types.Selector, error) {
	parts := strings.SplitAfterN(str, ":", 2)
	if len(parts) < 2 {
		return nil, fmt.Errorf("selector \"%s\" must be formatted as type:value", str)
	}

	s := &api_types.Selector{
		// Strip the trailing delimiter
		Type:  strings.TrimSuffix(parts[0], ":"),
		Value: parts[1],
	}
	return s, nil
}
